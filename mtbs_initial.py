# Initial Processing Script for Open Source MTBS  v 1.5.6E
# This version is heavily modified for bulk processing specific to EROS needs
# It has some functionality stripped out for efficiency

# Final output directory where final products are copied to before being deleted locally
copy_path = 'V:\\rdas_change_detection\\img_src\\landsat'
# copy_path = 'D:\\MTBS\\fire'
# All other directory usage is relative to the script location
# Make sure that your current working directory is the script location as well

#
# Kelcy Smith
# Charles F. Day LLC
# Contractor to USGS EROS
# Work performed under USGS contract G10PC00044
# klsmith@usgs.gov
#
# Computes TOA and NBR rasters for use in MTBS processing
# Input is tarball from GLOVIS or Earth Explorer
# Utilizes a directory structure that is relative to the script location
# Pixel values will deviate from regular MTBS processing due to using GDAL instead of ERDAS/ARC
#
# Tested/Designed to go from UTM to Albers CONUS, unsigned 8 bit
# Other projection/data type combinations used/added could cause un-intended behavior, provided as-is
#
# Batch Usage: file bit proj
#
# References:
# http://landsathandbook.gsfc.nasa.gov/data_prod/prog_sect11_3.html
# http://landsathandbook.gsfc.nasa.gov/pdfs/L5TMLUTIEEE2003.pdf
# http://landsat.usgs.gov/Landsat8_Using_Product.php
#
# Functionality referenced against PERL/ERDAS scripts developed by:
# Mike Coan
# SGT Inc.
# Contractor to USGS EROS
# Work Performed under USGS contract G10PC00044
# October 2008
#
# Revision History:
# 21-Jan-2015 1.0 Initial development complete
# 22-Jan-2015 1.1 Fixed some systemic problems with TOA outputs involving numpy
# Suppressed divide by zero Numpy warnings, Numpy handles these internally as 0
# 05-Feb-2015 1.2 Revised the handling and processing of the arrays to be more memory friendly
# Made it more backwards friendly with older versions of python and GDAL
# Let Numpy display warnings again as part of older Python compatibility
# 13-Feb-2015 1.3 Added Landsat 8 support
# 04-Mar-2015 1.4 Replaced first gdalwarp with projection calculations
# Fixed output formatting to more closely match current MTBS processing
# Added pyramids output
# Added Gap Mask output for Landsat 7
# 11-Mar-2015 1.5 Fixed extent snapping
# UTM works properly again

# EROS Version:
# 13-Mar-2015 1.5.0 Streamlined for bulk processing specific to certain needs
# 16-Mar-2015 1.5.1 Added support for NLAPS products
# Fixed Gain/Bias being applied to the wrong bands for LS 8
# 18-Mar-2015 1.5.2 Changed how NLAPS metadata is processed
# 21-Apr-2015 1.5.3 Support for different metadata formating used in SCENE_CENTER_TIME
# 29-Jun-2015 1.5.4 Gapmask is now only applied to NBR output, gap values are -32768 to match other MTBS processing
# 10-Jul-2015 1.5.5 Gapmask is now replaced by a no data mask derived from initial L1 data and applied to all bands after re-projection
#                           No data mask is buffered by 2 pixels and then re-projected with nearest neighbor
# 23-Jul-2015 Kept UTM relfectance product
# 24-Jul-2015 Added in projections for Alaska, Hawaii, and Puerto Rico / Virgin Islands

# TODO Revise commandline argument parsing
# TODO Add more documentation to each step and def
# TODO Clean up, lots of clean up
# TODO Continue to make the script more OS agnostic

import os
import subprocess
import sys
import itertools
import math
import time
import datetime
import linecache
import csv
import re
import shutil

from osgeo import gdal
from osgeo import osr
import numpy as np
import scipy
import scipy.ndimage as nd


# Used to align coordinates to a specific grid
def fifteen_offset(coord):
    return math.floor(coord / 30.0) * 30.0 + 15


# exoatmospheric values provided by the landsat handbooks
# band6 = landsat band 7
def esun_lookup(ls_sensor):
    esun_7 = {'band1': 1969.0,
              'band2': 1840.0,
              'band3': 1551.0,
              'band4': 1044.0,
              'band5': 225.7,
              'band6': 82.07}

    esun_5 = {'band1': 1957.0,
              'band2': 1826.0,
              'band3': 1554.0,
              'band4': 1036.0,
              'band5': 215.0,
              'band6': 80.67}

    esun_4 = {'band1': 1957.0,
              'band2': 1825.0,
              'band3': 1557.0,
              'band4': 1033.0,
              'band5': 214.9,
              'band6': 80.72}

    if ls_sensor == '7':
        return esun_7
    elif ls_sensor == '5':
        return esun_5
    elif ls_sensor == '4':
        return esun_4
    else:
        return 0


# calculate earth-sun distance based on date and time
def calc_au(date, scene_time):
    year, month, day = date.split('-')
    hour, min, sec = re.findall("\d+[\.]?\d*", scene_time)
    second = float(sec)

    t1 = 367 * int(year)
    t2 = int((int(month) + 9) / 12)
    t3 = int(7 * (int(year) + t2) / 4)
    t4 = int(275 * int(month) / 9)
    d = t1 - t3 + t4 + int(day) - 730530 + (
                                               int(hour) + int(min) / 60 + int(second) / 3600) / 24
    e = 0.016709 - 0.000000001151 * d
    m = 356.0470 + 0.9856002585 * d
    m -= int(m / 360) * 360
    mrad = m * pi / 180
    E = mrad + e * math.sin(mrad) * (1 + e * math.cos(mrad))
    xv = math.cos(E) - e
    yv = math.sqrt(1 - e * e) * math.sin(E)
    r = math.sqrt(xv * xv + yv * yv)

    return r


# gathers all needed information from the metadata file that comes with a Glovis product
def proc_meta(file_name, lsat_sensor):
    if lsat_sensor == '8':
        refl_rad = 'REFLECTANCE'
    else:
        refl_rad = 'RADIANCE'
    meta_file = open(file_name, 'r')
    meta_out = {}
    for line in meta_file:
        line_ls = line.split()

        if line_ls[0] == 'SCENE_CENTER_TIME':
            meta_out['scene_time'] = line_ls[2]
        elif line_ls[0] == 'DATE_ACQUIRED':
            meta_out['date_acq'] = line_ls[2]
        elif line_ls[0] == 'SUN_AZIMUTH':
            meta_out['sun_az'] = line_ls[2]
        elif line_ls[0] == 'SUN_ELEVATION':
            meta_out['sun_el'] = line_ls[2]

        elif line_ls[0] == '%s_MULT_BAND_1' % refl_rad:
            meta_out['mult_1'] = line_ls[2]
        elif line_ls[0] == '%s_MULT_BAND_2' % refl_rad:
            meta_out['mult_2'] = line_ls[2]
        elif line_ls[0] == '%s_MULT_BAND_3' % refl_rad:
            meta_out['mult_3'] = line_ls[2]
        elif line_ls[0] == '%s_MULT_BAND_4' % refl_rad:
            meta_out['mult_4'] = line_ls[2]
        elif line_ls[0] == '%s_MULT_BAND_5' % refl_rad:
            meta_out['mult_5'] = line_ls[2]
        elif line_ls[0] == '%s_MULT_BAND_6' % refl_rad:
            meta_out['mult_6'] = line_ls[2]
        elif line_ls[0] == '%s_MULT_BAND_7' % refl_rad:
            meta_out['mult_7'] = line_ls[2]
        elif line_ls[0] == '%s_MULT_BAND_8' % refl_rad:
            meta_out['mult_8'] = line_ls[2]
        elif line_ls[0] == '%s_MULT_BAND_9' % refl_rad:
            meta_out['mult_9'] = line_ls[2]

        elif line_ls[0] == '%s_ADD_BAND_1' % refl_rad:
            meta_out['add_1'] = line_ls[2]
        elif line_ls[0] == '%s_ADD_BAND_2' % refl_rad:
            meta_out['add_2'] = line_ls[2]
        elif line_ls[0] == '%s_ADD_BAND_3' % refl_rad:
            meta_out['add_3'] = line_ls[2]
        elif line_ls[0] == '%s_ADD_BAND_4' % refl_rad:
            meta_out['add_4'] = line_ls[2]
        elif line_ls[0] == '%s_ADD_BAND_5' % refl_rad:
            meta_out['add_5'] = line_ls[2]
        elif line_ls[0] == '%s_ADD_BAND_6' % refl_rad:
            meta_out['add_6'] = line_ls[2]
        elif line_ls[0] == '%s_ADD_BAND_7' % refl_rad:
            meta_out['add_7'] = line_ls[2]
        elif line_ls[0] == '%s_ADD_BAND_8' % refl_rad:
            meta_out['add_8'] = line_ls[2]
        elif line_ls[0] == '%s_ADD_BAND_9' % refl_rad:
            meta_out['add_9'] = line_ls[2]

    return meta_out


# used to transform, and determine the coordinates to snap the raster to
def get_coords(tif_file, proj_str):
    coord_ls = []

    t_ds = gdal.Open(tif_file)
    t_band = t_ds.GetRasterBand(1)
    t_rows = t_band.YSize
    t_cols = t_band.XSize
    t_proj = t_ds.GetProjectionRef()
    t_geo = t_ds.GetGeoTransform()

    albers_proj = osr.SpatialReference()
    albers_proj.ImportFromProj4(proj_str)

    from_proj = osr.SpatialReference()
    from_proj.ImportFromWkt(t_proj)

    coord_trans = osr.CoordinateTransformation(from_proj, albers_proj)

    ll = coord_trans.TransformPoint(t_geo[0], (t_geo[3] + t_geo[5] * t_rows))
    ul = coord_trans.TransformPoint(t_geo[0], t_geo[3])
    ur = coord_trans.TransformPoint((t_geo[0] + t_geo[1] * t_cols), t_geo[3])
    lr = coord_trans.TransformPoint((t_geo[0] + t_geo[1] * t_cols),
                                    (t_geo[3] + t_geo[5] * t_rows))

    x_min = min(ll[0], ul[0])
    y_min = min(ll[1], lr[1])
    x_max = max(lr[0], ur[0])
    y_max = max(ul[1], ur[1])

    # Determine the extents to keep consistent (xmin ymin xmax ymax)
    coord_ls.append(str(fifteen_offset(x_min)))
    coord_ls.append(str(fifteen_offset(y_min)))
    coord_ls.append(str(fifteen_offset(x_max)))
    coord_ls.append(str(fifteen_offset(y_max)))

    t_band = None
    t_ds = None

    return coord_ls


def apply_mask(mk_path, toa_path):
    mk_ds = gdal.Open(mk_path)
    t_ds = gdal.Open(toa_path, gdal.GA_Update)
    r = t_ds.RasterYSize
    c = t_ds.RasterXSize

    for x in range(1, t_ds.RasterCount + 1):
        m_arr = np.array(mk_ds.GetRasterBand(x).ReadAsArray(0, 0, c, r), dtype=np.uint8)
        t_arr = np.array(t_ds.GetRasterBand(x).ReadAsArray(0, 0, c, r), dtype=np.uint8)

        t_arr[(m_arr == 1) & (t_arr == 0)] = 1
        t_arr[m_arr == 0] = 0

        t_ds.GetRasterBand(x).WriteArray(t_arr)
        t_ds.FlushCache()

    mk_ds = None
    t_ds = None


def buffer_mask(mk_path):
    mk_ds = gdal.Open(mk_path, gdal.GA_Update)
    r = mk_ds.RasterYSize
    c = mk_ds.RasterXSize

    struct = nd.generate_binary_structure(2, 2)
    for x in range(1, mk_ds.RasterCount + 1):
        band = mk_ds.GetRasterBand(x)
        m_arr = np.array(band.ReadAsArray(0, 0, c, r), dtype=np.int)
        buff_arr = np.logical_not(
            nd.binary_dilation(np.logical_not(m_arr.astype(np.bool)), structure=struct,
                               iterations=2).astype(np.int))

        band.WriteArray(buff_arr)
        band = None

    mk_ds = None


def create_raster(in_arr, path, row, col, geo_coords, projection, bands):
    gdriver = gdal.GetDriverByName("GTiff")
    new_ds = gdriver.Create(path, col, row, bands, gdal.GDT_Int16)

    new_ds.SetProjection(projection)
    new_ds.SetGeoTransform(geo_coords)

    new_band = new_ds.GetRasterBand(1)
    new_band.WriteArray(in_arr)

    new_ds.BuildOverviews("CUBIC", overviewlist=[2, 4, 8, 16, 32])

    new_band = None
    new_ds = None


def proc_nlaps(nlaps_file):
    meta_out = {}

    nlaps = open(nlaps_file, 'r')

    for line in nlaps:
        line_ls = line.split()

        if not line_ls:
            continue

        if line[:13] == 'Sun Elevation':
            meta_out['sun_el'] = line_ls[2]
            meta_out['sun_az'] = line_ls[6]

        elif line[:17] == 'Scene center date':
            meta_out['date_acq'] = line_ls[3] + '-' + line_ls[4] + '-' + line_ls[5]
            meta_out['scene_time'] = line_ls[9] + 'z'

        elif line.rstrip() == '	      RADIOMETRIC CORRECTION':
            break

    for line in itertools.islice(nlaps, 5, 14):
        line_ls = line.split()
        if line_ls[0] == '1':
            meta_out['mult_1'] = line_ls[3]
            meta_out['add_1'] = line_ls[4]
        elif line_ls[0] == '2':
            meta_out['mult_2'] = line_ls[3]
            meta_out['add_2'] = line_ls[4]
        elif line_ls[0] == '3':
            meta_out['mult_3'] = line_ls[3]
            meta_out['add_3'] = line_ls[4]
        elif line_ls[0] == '4':
            meta_out['mult_4'] = line_ls[3]
            meta_out['add_4'] = line_ls[4]
        elif line_ls[0] == '5':
            meta_out['mult_5'] = line_ls[3]
            meta_out['add_5'] = line_ls[4]
        elif line_ls[0] == '7':
            meta_out['mult_7'] = line_ls[3]
            meta_out['add_7'] = line_ls[4]

    nlaps.close()

    return meta_out


def log_me(log_info):
    start = str(log_info[0].hour) + ':' + str(log_info[0].minute) + ':' + str(
        log_info[0].second)
    end = str(log_info[1].hour) + ':' + str(log_info[1].minute) + ':' + str(log_info[1].second)
    scene_file = log_info[2].rstrip()
    log_file_path = os.path.join(os.getcwd(), 'mtbs_log_%s-%s-%s.csv' % (
        log_info[3].year, log_info[3].month,
        log_info[3].day))
    log_file = open(log_file_path, 'a')
    log_writer = csv.writer(log_file, delimiter=',')
    csv_row = (start, end, scene_file)
    log_writer.writerow(csv_row)
    log_file.close()


pi = math.pi

FNULL = open(os.devnull, 'w')

# Pathing
base = os.path.dirname(os.path.realpath(__file__))
output_path = os.path.join(base, 'output')
work_path = os.path.join(base, 'working')
zip_path = os.path.join(base, 'tools', '7z')
gz_path = os.path.join(base, 'targz')
gdal_path = os.path.join(base, 'mtbs_env', 'Lib', 'site-packages', 'osgeo')

t0 = time.time()
d0 = datetime.datetime.now()
driver = gdal.GetDriverByName("GTiff")

for files in os.listdir(work_path):
    try:
        os.remove(os.path.join(work_path, files))
    except:
        print 'Unable to remove %s from working directory' % files
        continue

for file in os.listdir(gz_path):
    d1 = datetime.datetime.now()
    t1 = time.time()
    if file[-2:] != 'gz':
        continue

    scene_id = file[:-7]
    sensor = scene_id[2]
    gz_file = os.path.join(gz_path, file)
    tar_file = os.path.join(work_path, file[:-3])

    copy2_path = os.path.join(copy_path, scene_id[4:6] + scene_id[7:9], scene_id[2:-5])

    if not os.path.exists(output_path):
        subprocess.call('mkdir %s' % output_path, shell=True)

    print '\nProcessing ', gz_file

    # Empty the contents of the tarball into the working directory
    print "Unpacking everything..."
    subprocess.call('%s e -y -o%s -w%s %s' % (zip_path, work_path, work_path, gz_file),
                    stdout=FNULL, stderr=subprocess.STDOUT)
    subprocess.call('%s e -y -o%s -w%s %s' % (zip_path, work_path, work_path, tar_file),
                    stdout=FNULL, stderr=subprocess.STDOUT)
    os.remove(tar_file)

    print 'Building band stacks...'
    band_files = sorted(os.listdir(work_path))
    band_name = band_files[0][:-7]
    # Build a list of the different bands to be merged together into a stack
    bandList = []
    if sensor == '8':
        for i in range(7):
            bandList.append(os.path.join(work_path, (band_name + '_B' + str(i + 1) + '.tif ')))
        bandList.append(os.path.join(work_path, (band_name + '_B9.tif ')))
    else:
        for i in range(5):
            bandList.append(os.path.join(work_path, (band_name + '_B' + str(i + 1) + '.tif ')))
        bandList.append(os.path.join(work_path, (band_name + '_B7.tif ')))
    mask_path = os.path.join(work_path, scene_id + '_GM.tif')

    # Build VRT for TOA processing
    vrt_path = os.path.join(work_path, scene_id + '.vrt')

    subprocess.call(('%s/gdalbuildvrt -separate %s %s' % (gdal_path, vrt_path, ''.join(bandList))),
                    shell=True)

    # Grab meta data information for TOA processing
    if os.path.exists(os.path.join(work_path, band_name + '_WO.txt')):
        meta_dict = proc_nlaps(os.path.join(work_path, band_name + '_WO.txt'))
    else:
        meta_dict = proc_meta(os.path.join(work_path, (scene_id + '_MTL.txt')), sensor)

    # TOA processing
    print 'Computing TOA...'
    ds = gdal.Open(vrt_path)
    rows = ds.RasterYSize
    cols = ds.RasterXSize
    geo = ds.GetGeoTransform()
    projection = ds.GetProjection()

    toa_out_path = os.path.join(work_path, scene_id[2:-5] + '_UTM.TIF')

    if sensor == '8':
        toa_ds = driver.Create(toa_out_path, cols, rows, 8, gdal.GDT_Byte,
                               ['TILED=YES', 'BLOCKXSIZE=64', 'BLOCKYSIZE=64'])
        mask_ds = driver.Create(mask_path, cols, rows, 8, gdal.GDT_Byte)
    else:
        toa_ds = driver.Create(toa_out_path, cols, rows, 6, gdal.GDT_Byte,
                               ['TILED=YES', 'BLOCKXSIZE=64', 'BLOCKYSIZE=64'])
        mask_ds = driver.Create(mask_path, cols, rows, 6, gdal.GDT_Byte)

    toa_ds.SetGeoTransform(geo)
    mask_ds.SetGeoTransform(geo)
    toa_ds.SetProjection(projection)
    mask_ds.SetProjection(projection)

    if sensor != '8':
        esun = esun_lookup(sensor)
        au = calc_au(meta_dict['date_acq'], meta_dict['scene_time'])
    cos_zen = math.cos((90 - float(meta_dict['sun_el'])) * pi / 180)

    # Process each band, one at a time
    for num in range(8):
        num += 1

        if sensor != '8' and num > 6:
            continue

        band = ds.GetRasterBand(num)
        toa_band = toa_ds.GetRasterBand(num)
        mask_band = mask_ds.GetRasterBand(num)

        b_arr = np.array(band.ReadAsArray(0, 0, cols, rows), dtype=np.float32)
        mask_arr = np.zeros((rows, cols), dtype=np.bool)
        mask_arr[b_arr > 0] = 1
        del band

        if sensor == '8':
            mult = 400 / cos_zen

            if num == 8:  # Landsat 8 band 9 is band 8 in the stack
                num += 1
        else:
            mult = np.pi * au ** 2 / (esun['band%s' % num] * cos_zen) * 400

            if num == 6:  # The Landsat 4/5/7 band 7 is band 6 in the stack
                num += 1

        b_arr[b_arr > 0] *= float(meta_dict['mult_%s' % num])
        b_arr[b_arr > 0] += float(meta_dict['add_%s' % num])
        b_arr[b_arr > 0] *= mult

        b_arr[b_arr > 255] = 255
        b_arr = np.ceil(b_arr)

        toa_band.WriteArray(b_arr.astype(np.uint8))
        mask_band.WriteArray(mask_arr)
        del toa_band
        del mask_band

    del b_arr
    del mask_arr
    # del check_arr
    ds = None
    toa_ds = None
    mask_ds = None

    shutil.copy(toa_out_path, output_path)

    buffer_mask(mask_path)
    mask_out_path = os.path.join(output_path, scene_id[2:-5] + '_GM.TIF')

    path = int(scene_id[3:6])
    row = int(scene_id[6:9])

    if path > 60:  # Hawaii
        proj4_str = '+proj=aea +lat_1=8 +lat_2=18 +lat_0=3 +lon_0=-157 +x_0=0 +y_0=0 +ellps=GRS80 +datum=NAD83 +units=m +no_defs'
    elif row > 44 and path < 10:  # Puerto Rico
        proj4_str = '+proj=aea +lat_1=8 +lat_2=18 +lat_0=3 +lon_0=-66 +x_0=0 +y_0=0 +ellps=GRS80 +datum=NAD83 +units=m +no_defs'
    elif row < 20 and path > 50:  # Alaska
        proj4_str = '+proj=aea +lat_1=55 +lat_2=65 +lat_0=50 +lon_0=-154 +x_0=0 +y_0=0 +ellps=GRS80 +datum=NAD83 +units=m +no_defs'
    else:
        proj4_str = '+proj=aea +lat_1=29.5 +lat_2=45.5 +lat_0=23 +lon_0=-96 +datum=NAD83 +units=m +no_defs'

    gdal_str = "-t_srs \"%s\"" % proj4_str

    # Merge then warp the stack to the output directory
    print 'Projecting...'
    proj_out_path = os.path.join(output_path, scene_id[2:-5] + '_REFL.TIF')
    box_ls = get_coords(bandList[0], proj4_str)

    subprocess.call('%s/gdalwarp -r cubic -tr 30 30 -te %s %s %s %s %s %s %s' % (
        gdal_path,
        box_ls[0], box_ls[1], box_ls[2],
        box_ls[3], gdal_str,
        toa_out_path, proj_out_path),
                    shell=True)

    subprocess.call('%s/gdalwarp -r near -tr 30 30 -te %s %s %s %s %s %s %s %s' % (
        gdal_path,
        box_ls[0], box_ls[1], box_ls[2],
        box_ls[3], gdal_str,
        '-ot Byte', mask_path,
        mask_out_path), shell=True)

    apply_mask(mask_out_path, proj_out_path)
    os.remove(mask_out_path)
    print 'Computing NBR...'

    toa_ds = gdal.Open(proj_out_path)
    geo = toa_ds.GetGeoTransform()
    projection = toa_ds.GetProjection()
    cols = toa_ds.RasterXSize
    rows = toa_ds.RasterYSize

    gdal.SetConfigOption('TIFF_USE_OVR', 'YES')
    toa_ds.BuildOverviews("CUBIC", overviewlist=[2, 4, 8, 16, 32])

    # Let numpy handle division by 0, but don't output an error message
    with np.errstate(invalid='ignore'):
        if sensor == '8':
            band5 = np.array(toa_ds.GetRasterBand(5).ReadAsArray(0, 0, cols, rows),
                             dtype=np.float16)
            band7 = np.array(toa_ds.GetRasterBand(7).ReadAsArray(0, 0, cols, rows),
                             dtype=np.float16)
            nbr_band = (band5 - band7) / (band5 + band7) * 1000
            nbr_band[(band5 == 0) | (band7 == 0)] = -32768

            del band5, band7
        else:
            band4 = np.array(toa_ds.GetRasterBand(4).ReadAsArray(0, 0, cols, rows),
                             dtype=np.float16)
            band6 = np.array(toa_ds.GetRasterBand(6).ReadAsArray(0, 0, cols, rows),
                             dtype=np.float16)
            nbr_band = (band4 - band6) / (band4 + band6) * 1000
            nbr_band[(band4 == 0) | (band6 == 0)] = -32768

            del band4, band6

    toa_ds = None

    nbr_out_path = os.path.join(output_path, scene_id[2:-5] + '_NBR.TIF')
    if os.path.exists(nbr_out_path):
        os.remove(nbr_out_path)

    create_raster(nbr_band, nbr_out_path, rows, cols, geo, projection, 1)
    del nbr_band

    print 'Computing statistics and histogram...'
    subprocess.call('%s/gdalinfo -hist -stats %s' % (gdal_path, proj_out_path), shell=True, stdout=FNULL,
                    stderr=subprocess.STDOUT)
    subprocess.call('%s/gdalinfo -hist -stats %s' % (gdal_path, nbr_out_path), shell=True, stdout=FNULL,
                    stderr=subprocess.STDOUT)

    subprocess.call('xcopy /F /Y /I %s %s' % (output_path, copy2_path), shell=True)
    print 'Clean up...'
    for files in os.listdir(work_path):
        try:
            os.remove(os.path.join(work_path, files))
        except:
            continue

    for files in os.listdir(output_path):
        try:
            os.remove(os.path.join(output_path, files))
        except:
            continue

    try:
        os.remove(gz_file)
    except:
        print 'Unable to delete ', gz_file
        pass

    log_me((d1, datetime.datetime.now(), scene_id, d0))
    print 'Finished!', time.time() - t1

print '\nFinished processing all files, total time: ', time.time() -t0
