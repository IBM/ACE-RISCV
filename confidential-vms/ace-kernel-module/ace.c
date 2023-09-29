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

static ulong address = 0x80000000;
static ulong size = 0x1;

module_param(address, ulong, 0660);
module_param(size, ulong, 0660);

static int ace_init(void){
    ulong i;
    uint64_t volatile *virt_addr;
    uint64_t value;

    printk(KERN_WARNING "ACE: Reading addresses: 0x%lx - 0x%lx", address, address+size);

    for (i=0; i<size; i+=1) { 
        virt_addr = (uint64_t *) ioremap(address+i, 8);
        value = (*virt_addr);
        printk(KERN_WARNING "%lx: %llx\n", address+i, value);
    }

	return 0;
}

static void ace_exit(void){
}

module_init(ace_init);
module_exit(ace_exit);