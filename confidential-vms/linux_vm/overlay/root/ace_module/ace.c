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
#include <linux/init.h>
#include <linux/module.h>
#include <linux/cdev.h>
#include <linux/device.h>
#include <linux/kernel.h>
#include <linux/uaccess.h>
#include <linux/fs.h>

#define MAX_DEV 2

static int mychardev_open(struct inode *inode, struct file *file);
static int mychardev_release(struct inode *inode, struct file *file);
static long mychardev_ioctl(struct file *file, unsigned int cmd, unsigned long arg);
static ssize_t mychardev_read(struct file *file, char __user *buf, size_t count, loff_t *offset);
static ssize_t mychardev_write(struct file *file, const char __user *buf, size_t count, loff_t *offset);

static const struct file_operations mychardev_fops = {
    .owner      = THIS_MODULE,
    .open       = mychardev_open,
    .release    = mychardev_release,
    .unlocked_ioctl = mychardev_ioctl,
    .read       = mychardev_read,
    .write       = mychardev_write
};

struct mychar_device_data {
    struct cdev cdev;
};

static int dev_major = 0;
static struct class *mychardev_class = NULL;
static struct mychar_device_data mychardev_data[MAX_DEV];

static int mychardev_uevent(struct device *dev, struct kobj_uevent_env *env)
{
    add_uevent_var(env, "DEVMODE=%#o", 0666);
    return 0;
}

static int __init mychardev_init(void)
{
    int err, i;
    dev_t dev;

    err = alloc_chrdev_region(&dev, 0, MAX_DEV, "mychardev");

    dev_major = MAJOR(dev);

    mychardev_class = class_create(THIS_MODULE, "mychardev");
    mychardev_class->dev_uevent = mychardev_uevent;

    for (i = 0; i < MAX_DEV; i++) {
        cdev_init(&mychardev_data[i].cdev, &mychardev_fops);
        mychardev_data[i].cdev.owner = THIS_MODULE;

        cdev_add(&mychardev_data[i].cdev, MKDEV(dev_major, i), 1);

        device_create(mychardev_class, NULL, MKDEV(dev_major, i), NULL, "mychardev-%d", i);
    }

    return 0;
}

static void __exit mychardev_exit(void)
{
    int i;

    for (i = 0; i < MAX_DEV; i++) {
        device_destroy(mychardev_class, MKDEV(dev_major, i));
    }

    class_unregister(mychardev_class);
    class_destroy(mychardev_class);

    unregister_chrdev_region(MKDEV(dev_major, 0), MINORMASK);
}

static int mychardev_open(struct inode *inode, struct file *file)
{
    printk("MYCHARDEV: Device open\n");
    return 0;
}

static int mychardev_release(struct inode *inode, struct file *file)
{
    printk("MYCHARDEV: Device close\n");
    return 0;
}

static long mychardev_ioctl(struct file *file, unsigned int cmd, unsigned long arg)
{
    printk("MYCHARDEV: Device ioctl\n");
    return 0;
}

static ssize_t mychardev_read(struct file *file, char __user *buf, size_t count, loff_t *offset)
{
    // uint8_t *data = "Hello from the kernel world!\n";
    // size_t datalen = strlen(data);
    uint8_t data[64];
    unsigned long cycles = csr_read(CSR_TIME);
    sprintf(data, "%ld", cycles);

    // printk("Reading device: %d\n", MINOR(file->f_path.dentry->d_inode->i_rdev));

    // if (count > datalen) {
    //     count = datalen;
    // }

    if (copy_to_user(buf, data, 64)) {
        return -EFAULT;
    }

    return count;
}

static ssize_t mychardev_write(struct file *file, const char __user *buf, size_t count, loff_t *offset)
{
    size_t maxdatalen = 30, ncopied;
    uint8_t databuf[maxdatalen];

    printk("Writing device: %d\n", MINOR(file->f_path.dentry->d_inode->i_rdev));

    if (count < maxdatalen) {
        maxdatalen = count;
    }

    ncopied = copy_from_user(databuf, buf, maxdatalen);

    if (ncopied == 0) {
        printk("Copied %zd bytes from the user\n", maxdatalen);
    } else {
        printk("Could't copy %zd bytes from the user\n", ncopied);
    }

    databuf[maxdatalen] = 0;

    printk("Data from the user: %s\n", databuf);

    return count;
}




// static int ace_init(void){
//     volatile u8 *secret;
//     struct sbiret ret;
//     int i;

//     printk(KERN_ALERT "Requesting secret from the security monitor\n");
//     secret = kmalloc(1024*sizeof(u8), GFP_KERNEL);
//     ret = sbi_ecall(0x434F5647, 9, virt_to_phys((void *) secret), 1024, 0, 0, 0, 0);
//     if (!ret.error) {
//         printk(KERN_ALERT "Secret=0x");
//         for (i=0; i<ret.value; i++) {
//             printk(KERN_CONT "%02x", secret[i]);
//         }
//         printk(KERN_CONT "\n");
//     } else {
//         printk(KERN_ALERT "Error: %lx %lx", ret.error, ret.value);
//     }
// 	return 0;
// }

// static void ace_exit(void){
// }

// module_init(ace_init);
// module_exit(ace_exit);

module_init(mychardev_init);
module_exit(mychardev_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Wojciech Ozga <woz@zurich.ibm.com>");
