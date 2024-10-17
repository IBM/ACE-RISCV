#include<linux/init.h>
#include<linux/module.h>
#include <asm/sbi.h>
#include <linux/io.h>
#include <linux/kernel.h>
#include <linux/debugfs.h>
#include <linux/delay.h> /* usleep_range */
#include <linux/kthread.h>
#include <linux/seq_file.h> /* single_open, single_release */
#include <linux/slab.h> /* kmalloc, kfree */

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Wojciech Ozga <woz@zurich.ibm.com>");

static int ace_init(void){
    volatile u8 *secret;
    struct sbiret ret;
    int i;

    printk(KERN_ALERT "Requesting secret from the security monitor\n");    
    secret = kmalloc(1024*sizeof(u8), GFP_KERNEL);
    ret = sbi_ecall(0x434F5647, 9, virt_to_phys((void *) secret), 1024, 0, 0, 0, 0);
    if (!ret.error) {
        printk(KERN_ALERT "Secret=0x");
        for (i=0; i<ret.value; i++) {
            printk(KERN_CONT "%02x", secret[i]);
        }
        printk(KERN_CONT "\n");
    } else {
        printk(KERN_ALERT "Error: %lx %lx", ret.error, ret.value);
    }
	return 0;
}

static void ace_exit(void){
}

module_init(ace_init);
module_exit(ace_exit);