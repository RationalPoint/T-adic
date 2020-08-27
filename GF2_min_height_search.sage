r"""

Sage script to find all irreducible totally T-adic polynomials over GF(2) of
minimum height 1/3 and gonality n 

Strategy:
1. Initial search space is 2n^2 + 3n - 3 bits
2. Use linear algebra to cut the search space down to 2n^2 - n - 3 bits
3. Break the search space into tiles and hand it off to separate processes.

For the case n = 4, initial search space is 41 bits. Reduced search space is 25
bits. If we break the space into 32 tiles, this cuts the search space down to 20
bits per Sage instance, which is readily manageable. 

Use sage_launcher.py to handle launching the separate sage processes as follows:

$ python3 sage_launch.py -c -o tile GF2_min_height_search.sage [data directory] [number of tiles]

The sage_launcher.py script will create the specified data directory. The number
of tiles is best set to a power of 2 for load balancing. To test the script on a
smaller problem, change the value of n (below) to 3 and set the number of tiles
to 2 or 4 during launch. The case n=4 took around a day when broken into 32
tiles on a compute server with many CPUs.

"""

# Modify only up to the next row of hashes

n = 4 # Gonality of the elements of minimum height to be determined
steps_until_print=2**10

################################################################################

import argparse
import Tadic

parser = argparse.ArgumentParser()
parser.add_argument('num_jobs',type=int,help='break up work into this many jobs')
parser.add_argument('job',type=int,help='which job is the current one?')
parser.add_argument('filename',type=str,help='where to write output')
args = parser.parse_args()

################################################################################

print('Searching for totally T-adic elements of height 1/3 and gonality n = {}'.format(n))
kwargs = {}
kwargs['num_jobs'] = args.num_jobs
kwargs['job'] = args.job
kwargs['steps_until_print'] = steps_until_print

pols = Tadic.small_totally_T_adic_polys_GF2(n,**kwargs)
print('Found {} elements'.format(len(pols)))
fp = open(args.filename,'w')
for pol in pols:
  fp.write(str(pol) + '\n')
fp.close()
