from scipy import stats
import locale
import subprocess
import shlex
import os

ws='128'
alpha2 = 0.001
#calculate mean and var for eeach prime calling c program#
primes = ['7547', '7853', '14341', '14939', '16067', '22691', '25693',
    '27437', '35899', '36877', '52147', '57899', '89051', '96221', '152267']

if(os.path.isfile('pval.txt')):
    os.remove('pval.txt')

for p in primes:
    c_prog = ("./inverse_bench_" + p + " 0.05")
    commands = shlex.split(c_prog)

    proc1 = subprocess.Popen(commands)
    proc1.wait()

#start pvalue part#
f_in = open('pval.txt', 'r');
tables_file = open('table'+ws+'.txt', 'w');
result_file = open('res_pval'+ws+'.txt', 'w');
result_file.write('case 1 = $H_0 = mu1 -mu2 =0$\
   \n') # || case 2 = $H_0 = mu1 - mu2 !=0$ \



for p in primes: #(0,15)
    prime = f_in.readline()

    csv_file= open('csv_files/'+p+'_'+ ws +'.csv', 'w');

#tables file construction
    tables_file.write('\%'+prime+ '\n')
    tables_file.write('\\begin{table}[ht] \n')
    tables_file.write('\\centering \n')
    tables_file.write('\\caption{'+ p +' '+ws+ ' }\n')
    tables_file.write('\\begin{tabular}[t]{ccccc} \n')
    tables_file.write('\\toprule \n')
    tables_file.write('\\textbf{x} & \\textbf{pol avg}(Clock cycle) & \\textbf{pol var}(Clock cycle) & \\textbf{mon avg}(Clock cycle) & \\textbf{mon var}(Clock cycle) \\\\ \n')
    tables_file.write('\\midrule \n')

#result file construction
    result_file.write('\\begin{table}[ht] \n')
    result_file.write('\\centering \n')
    result_file.write('\\caption{'+ p +' '+ws+ ' }\n')
    result_file.write('\\begin{tabular}[t]{cccll} \n')
    result_file.write('\\toprule \n')
    result_file.write('\\textbf{x} & \\textbf{T} & \\textbf{pval} & \\textbf{test case1} & \\textbf{test case2}\\\\ \n')
    result_file.write('\\midrule \n')

#csv file construction
    csv_file.write( 'x,pol_avg,pol_var,mon_avg,mon_var,t\n')

#    alpha = 0.001
    for l in range(0,6):
        line = f_in.readline()
        (x, pol_avg, pol_var, mon_avg, mon_var, t)= line.split()

        pval = stats.t.sf(abs(locale.atof(t)), 198)*2

        result_file.write(x + ' & ' + t + ' & %6.4f'%(pval))
        if(pval > alpha2):
            result_file.write('& {\\cellcolor[HTML]{33CC33}} TEST OK (accept $H_0(case1)$)')
        else:
            result_file.write('& {\\cellcolor[HTML]{FF0000}} TEST FAIL (refuse $H_0(case1)$)')

#        if(pval < alpha2):
#            result_file.write('& {\\cellcolor[HTML]{33CC33}} TEST OK (refuse $H_0(case2)$)')
#        else:
#            result_file.write('& {\\cellcolor[HTML]{FF0000}} TEST FAIL (refuse $H_0(case2)$)')

        result_file.write("\\\\ \n")

        tables_file.write(x + ' & ' + pol_avg + ' & '+ pol_var + ' & ' + mon_avg+ ' & '+ mon_var + ' \\\\ \n')

        csv_file.write(x + ',' + pol_avg + ','+ pol_var + ',' + mon_avg+ ','+ mon_var + ','+t +'\n')


    print(p+"done \n")
    tables_file.write('\\bottomrule \n')
    tables_file.write('\\end{tabular} \n')
    tables_file.write('\\end{table} \n')
    tables_file.write('\n')

    result_file.write('\\bottomrule \n')
    result_file.write('\\end{tabular} \n')
    result_file.write('\\end{table} \n')
    result_file.write("\n")

    csv_file.close()

f_in.close()
tables_file.close()
result_file.close()
