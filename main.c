
/*
 *
 * Decompress dlpager_q6zip section
 *     tewilove@gmail.com, All rights reserved
 *
 */

#include <sys/types.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>
#include <memory.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define NELEM(x) (sizeof(x) / sizeof(x[0]))

#define BLOCK_SIZE 1024

#define ZIP20_DICT1_BITS 10
#define ZIP20_DICT2_BITS 14
#define ZIP20_DICT1_SIZE (1 << ZIP20_DICT1_BITS)
#define ZIP20_DICT2_SIZE (1 << ZIP20_DICT2_BITS)
#define ZIP20_DICT_SIZE (ZIP20_DICT1_SIZE + ZIP20_DICT2_SIZE)
#define ZIP20_LOOK_BACK_BITS 7

#define ZIP16_DICT1_BITS 10
#define ZIP16_DICT2_BITS 12
#define ZIP16_DICT1_SIZE (1 << ZIP16_DICT1_BITS)
#define ZIP16_DICT2_SIZE (1 << ZIP16_DICT2_BITS)
#define ZIP16_DICT_SIZE (ZIP16_DICT1_SIZE + ZIP16_DICT2_SIZE)
#define ZIP16_LOOK_BACK_BITS 9

#define ZIP8_DICT_SIZE 0x800

struct __attribute__ ((__packed__)) zip20_seg_hdr {
    uint16_t nb;
    uint16_t unknown;
    uint32_t dict[ZIP20_DICT_SIZE];
    uint32_t va[0];
};

struct __attribute__ ((__packed__)) zip16_seg_hdr {
    uint32_t nb;
    uint32_t dict[ZIP16_DICT_SIZE];
    uint32_t va[0];
};

struct __attribute__ ((__packed__)) zip8_seg_hdr {
    uint32_t nb;
    uint32_t dict[ZIP8_DICT_SIZE];
    uint32_t va[0];
};

const static uint32_t zip16_code_maps[] = {
    4,       // 0
    2,       // 1
    7,       // 2
    0,       // 3
    1,       // 4
    6,       // 5
    5,       // 6
    3,       // 7
    4,       // 8
    2,       // 9
    -1,      // 10
    0,       // 11
    1,       // 12
    -1,      // 13
    5,       // 14
    3,       // 15
};

const static uint32_t zip16_bits_maps[] = {
    3, // 0
    3, // 1
    3, // 2
    3, // 3
    3, // 4
    3, // 5
    4, // 6
    4, // 7
    5, // 8
    5, // 9
    6, // 10
    6, // 11
    6, // 12
    7, // 13
    7, // 14
};

static uint32_t bits_peek(uint32_t *ptr, uint32_t off, uint32_t nbs) {
    uint32_t val;

    if (nbs == 0 || nbs > 32)
        abort();
    if (off % 32 == 0) {
        if (nbs == 32)
            val = ptr[off / 32];
        else
            val = ptr[off / 32] & ((1UL << nbs) - 1);
    } else if (off / 32 == (off + nbs) / 32) {
        val = ptr[off / 32];
        off %= 32;
        val &= (1UL << (off + nbs)) - 1;
        if (off)
            val >>= off;
    } else {
        uint32_t v0, v1;
        uint32_t s0, s1;

        v0 = ptr[off / 32];
        v1 = ptr[(off + nbs) / 32];
        s0 = off % 32;
        s1 = (off + nbs) % 32;
        val = (v0 >> s0) | ((v1 & ((1 << s1) -1)) << (32 - s0));
    }

    return val;
}

static uint32_t bits_read(uint32_t *ptr, uint32_t *off, uint32_t nbs) {
    uint32_t val;

    val = bits_peek(ptr, *off, nbs);
    *off += nbs;

    return val;
}

#define BITS_PEEK(ptr, off, nbs) bits_peek((uint32_t *)(ptr), (uint32_t)(off), (uint32_t)(nbs))
#define BITS_READ(ptr, off, nbs) bits_read((uint32_t *)(ptr), (uint32_t *)(off), (uint32_t)(nbs))

static int uncompress_20(const uint32_t *dict1, const uint32_t *dict2, const void *ipt, void *opt) {
    int err = 0, x;
    const void *ipp = ipt;
    int ibo = 0;
    uint32_t *opp = (uint32_t *) opt;
    int idx = -1, idc = -1 & ~((1 << ZIP20_LOOK_BACK_BITS) - 1);
    uint32_t msk;

    memset(opt, 0, BLOCK_SIZE * sizeof(uint32_t));
	for (;;) {
        uint32_t sub, val = 0;

		val = BITS_PEEK(ipp, ibo, 4);
		if (val == 0b0000 || val == 0b1000) {
			BITS_READ(ipp, &ibo, 3);
			idx = idc | BITS_READ(ipp, &ibo, 7);
			msk = BITS_READ(ipp, &ibo, 8);
			val = (opp[idx] & 0xffffff00) | msk;
		} else if (val == 0b0001 || val == 0b1001) {
			BITS_READ(ipp, &ibo, 3);
			idx = idc | BITS_READ(ipp, &ibo, 7);
			val = opp[idx];
		} else if (val == 0b0010) {
			BITS_READ(ipp, &ibo, 4);
			idx = idc | BITS_READ(ipp, &ibo, 7);
			msk = BITS_READ(ipp, &ibo, 12);
			val = (opp[idx] & 0xfffff000) | msk;
		} else if (val == 0b0011 || val == 0b1011) {
			BITS_READ(ipp, &ibo, 3);
			val = BITS_READ(ipp, &ibo, 32);
		} else if (val == 0b0100 || val == 0b1100) {
			BITS_READ(ipp, &ibo, 3);
			val = dict1[BITS_READ(ipp, &ibo, 10)];
		} else if (val == 0b0101) {
			BITS_READ(ipp, &ibo, 4);
			val = dict2[BITS_READ(ipp, &ibo, 14)];
		} else if (val == 0b0110 || val == 0b1110) {
			BITS_READ(ipp, &ibo, 3);
			msk = BITS_READ(ipp, &ibo, 8);
			val = (opp[idx] & 0xffffff00) | msk;
		} else if (val == 0b0111 || val == 0b1111) {
			BITS_READ(ipp, &ibo, 3);
			val = opp[idx];
		} else if (val == 0b1010) {
			BITS_READ(ipp, &ibo, 4);
			sub = BITS_READ(ipp, &ibo, 2);
			if (sub == 3) {
				idx = idc | BITS_READ(ipp, &ibo, 7);
				msk = BITS_READ(ipp, &ibo, 8);
				val = (opp[idx] & 0xffff00ff) | (msk << 8);
			} else if (sub == 2) {
				idx = idc | BITS_READ(ipp, &ibo, 7);
				msk = BITS_READ(ipp, &ibo, 8);
				val = (opp[idx] & 0xff00ffff) | (msk << 16);
			} else if (sub == 0) {
				msk = BITS_READ(ipp, &ibo, 16);
				val = (opp[idx] & 0xffff0000) | msk;
			} else {
				x = BITS_READ(ipp, &ibo, 1);
				if (!x) {
					msk = BITS_READ(ipp, &ibo, 8);
					if (msk == 0xff) {
						break;
					}
					val = (opp[idx] & 0xff00ffff) | (msk << 16);
				} else {
					msk = BITS_READ(ipp, &ibo, 8);
					val = (opp[idx] & 0xffff00ff) | (msk << 8);
				}
			}
		} else if (val == 0b1101) {
			BITS_READ(ipp, &ibo, 4);
			x = BITS_READ(ipp, &ibo, 1);
			if (x == 0) {
				idx = idc | BITS_READ(ipp, &ibo, 7);
				msk = BITS_READ(ipp, &ibo, 16);
				val = (opp[idx] & 0xffff0000) | msk;
			} else {
				msk = BITS_READ(ipp, &ibo, 12);
				val = (opp[idx] & 0xfffff000) | msk;
			}
		} else {
			err = -1;
			break;
		}
		*opp++ = val;
		// printf("%d %08x\n", (void *)opp - opt, val);
	}

	return err;
}

static int uncompress_16(const uint32_t *dict1, const uint32_t *dict2, const void *ipt, void *opt) {
    int err = 0;
    const void *ipp = ipt;
    int ibo = 0;
    uint32_t *opp = (uint32_t *) opt;
    int idx = -1, idc = -1 & ~((1 << ZIP16_LOOK_BACK_BITS) - 1);
    uint32_t msk;

    memset(opt, 0, BLOCK_SIZE * sizeof(uint32_t));
    for (;;) {
        uint32_t type = (uint32_t) -1;
        uint32_t val = 0;
        
        val = BITS_PEEK(ipp, ibo, 4);
        if (val == 0b1010) {
            val = BITS_PEEK(ipp, ibo + 4, 2);
            if (val == 0b11)
                type = 11;
            else if (val == 0b10)
                type = 12;
            else if (val == 0b00)
                type = 10;
            else {
                val = BITS_PEEK(ipp, ibo + 6, 1);
                if (val == 0b1)
                    type = 13;
                else
                    type = 14;
            }
        } else if (val == 0b1101) {
            val = BITS_PEEK(ipp, ibo + 4, 1);
            if (val == 0b1)
                type = 9;
            else
                type = 8;
        } else {
            type = zip16_code_maps[val];
        }
        if (type == (uint32_t) -1) {
            err = 1;
            fprintf(stderr, "%s:%d", __func__, __LINE__);
            break;
        }
        // they are the same
        if (type == 14) {
            if ((void *)(opp) - opt >= BLOCK_SIZE * sizeof(uint32_t)) {
                type = 15;
            }
        }
        // 
        ibo += zip16_bits_maps[type];
        //
        switch(type) {
        case 3: {
            val = opp[idx];
            break;
        }
        case 2: {
            idx = idc | BITS_READ(ipp, &ibo, ZIP16_LOOK_BACK_BITS);
            val = opp[idx];
            break;
        }
        case 14: {
            msk = BITS_READ(ipp, &ibo, 8);
            val = (opp[idx] & 0xff00ffff) | (msk << 16);
            break;
        }
        case 12: {
            idx = idc | BITS_READ(ipp, &ibo, ZIP16_LOOK_BACK_BITS);
            msk = BITS_READ(ipp, &ibo, 8);
            val = (opp[idx] & 0xff00ffff) | (msk << 16);
            break;
        }
        case 13: {
            msk = BITS_READ(ipp, &ibo, 8);
            val = (opp[idx] & 0xffff00ff) | (msk << 8);
            break;
        }
        case 11: {
            idx = idc | BITS_READ(ipp, &ibo, ZIP16_LOOK_BACK_BITS);
            msk = BITS_READ(ipp, &ibo, 8);
            val = (opp[idx] & 0xffff00ff) | (msk << 8);
            break;
        }
        case 5: {
            msk = BITS_READ(ipp, &ibo, 8);
            val = (opp[idx] & 0xffffff00) | msk;
            break;
        }
        case 4: {
            idx = idc | BITS_READ(ipp, &ibo, ZIP16_LOOK_BACK_BITS);
            msk = BITS_READ(ipp, &ibo, 8);
            val = (opp[idx] & 0xffffff00) | msk;
            break;
        }
        case 9: {
            msk = BITS_READ(ipp, &ibo, 12);
            val = (opp[idx] & 0xfffff000) | msk;
            break;
        }
        case 7: {
            idx = idc | BITS_READ(ipp, &ibo, ZIP16_LOOK_BACK_BITS);
            msk = BITS_READ(ipp, &ibo, 12);
            val = (opp[idx] & 0xfffff000) | msk;
            break;
        }
        case 10: {
            msk = BITS_READ(ipp, &ibo, 16);
            val = (opp[idx] & 0xffff0000) | msk;
            break;
        }
        case 8: {
            idx = idc | BITS_READ(ipp, &ibo, ZIP16_LOOK_BACK_BITS);
            msk = BITS_READ(ipp, &ibo, 16);
            val = (opp[idx] & 0xffff0000) | msk;
            break;
        }
        case 6: {
            val = dict2[BITS_READ(ipp, &ibo, ZIP16_DICT2_BITS)];
            break;
        }
        case 1: {
            val = dict1[BITS_READ(ipp, &ibo, ZIP16_DICT1_BITS)];
            break;
        }
        case 0: {
            val = BITS_READ(ipp, &ibo, 32);
            break;
        }
        case 15: {
            break;
        }
        default: {
            err = 1;
            fprintf(stderr, "%s:%d\n", __func__, __LINE__);
            break;
        }
        }
        //
        if (err != 0)
            break;
        if (type == 15)
            break;
        //
        // printf("out: %x\n", val);
        *opp++ = val;
    }

    return err ? -1 : 0;
}

static int uncompress_8(const uint32_t *dict, const void *ipt, void *opt) {
    int err = 0, eos = 0;
    const void *ipp = ipt;
    int ibo = 0;
    uint32_t *opp = (uint32_t *) opt;
    int idx = -1;

    memset(opt, 0, BLOCK_SIZE * sizeof(uint32_t));
    for (;;) {
        uint32_t cmd, sub, val = 0;

        cmd = BITS_READ(ipp, &ibo, 2);
        if (cmd == 0b10) {
            // 0
            val = BITS_READ(ipp, &ibo, 32);
        } else if (cmd == 0b01) {
            // MATCH_DICT
            val = dict[BITS_READ(ipp, &ibo, 11)];
        } else if (cmd == 0b00) {
            if (BITS_READ(ipp, &ibo, 1)) {
                // REPEAT_LAST
                val = opp[idx];
            } else {
                // LOOK_BACK
                idx = -1 - BITS_READ(ipp, &ibo, 8);
                val = opp[idx];
            }
        } else {
            cmd = BITS_READ(ipp, &ibo, 3);
            idx = -1 - BITS_READ(ipp, &ibo, 8);
            switch (cmd) {
            case 0: {
                uint32_t msk;

                msk = BITS_READ(ipp, &ibo, 8);
                val = (opp[idx] & 0xffffff00) | msk;
                break;
            }
            case 1: {
                uint32_t msk;

                msk = BITS_READ(ipp, &ibo, 12);
                val = (opp[idx] & 0xfffff000) | msk;
                break;
            }
            case 2: {
                uint32_t xft1, xft2;

                xft1 = BITS_READ(ipp, &ibo, 4);
                xft2 = BITS_READ(ipp, &ibo, 3);
                val = opp[idx] ^ (1 << xft1) ^ (1 << (xft1 + xft2 + 1));
                break;
            }
            case 3: {
                uint32_t xft;

                xft = BITS_READ(ipp, &ibo, 4);
                val = opp[idx] ^ (1 << xft);
                break;
            }
            case 4: {
                uint32_t msk;

                msk = BITS_READ(ipp, &ibo, 16);
                val = (opp[idx] & 0xffff0000) | msk;
                break;
            }
            case 5: {
                uint32_t msk1, msk2;

                msk1 = BITS_READ(ipp, &ibo, 4);
                msk2 = BITS_READ(ipp, &ibo, 12);
                val = (opp[idx] & 0xff0ff000) | (msk1 << 20) | msk2;
                break;
            }
            case 6: {
                uint32_t msk1, msk2;

                ibo -= 8;
                sub = BITS_READ(ipp, &ibo, 2);
                idx = -1 - BITS_READ(ipp, &ibo, 8);
                if (sub == 0) {
                    msk1 = BITS_READ(ipp, &ibo, 8);
                    val = (opp[idx] & 0xffff00ff) | msk1;
                } else if (sub == 1) {
                    msk1 = BITS_READ(ipp, &ibo, 4);
                    msk2 = BITS_READ(ipp, &ibo, 8);
                    val = (opp[idx] & 0xfff0ff00) | (msk1 << 16) | msk2;
                } else if (sub == 2) {
                    msk1 = BITS_READ(ipp, &ibo, 16);
                    val = (opp[idx] & 0x0000ffff) | (msk1 << 16);
                } else if (sub == 3) {
                    msk1 = BITS_READ(ipp, &ibo, 8);
                    val = (opp[idx] & 0xff00ffff) | (msk1 << 16);
                }
                break;
            }
            case 7: {
                int idx1, idx2, idx3;
                uint32_t val1, val2, val3;

                ibo -= 8;
                sub = BITS_READ(ipp, &ibo, 2);
                if (sub == 0) {
                    idx1 = -1 - BITS_READ(ipp, &ibo, 8);
                    idx2 = -1 - BITS_READ(ipp, &ibo, 8);
                    idx3 = -1 - BITS_READ(ipp, &ibo, 8);
                    val1 = opp[idx1];
                    val2 = opp[idx2];
                    val3 = opp[idx3];
                    val = (val3 & 0x000001ff) | (val2 & 0x0001fe00) | (val1 & 0xfffe0000);
                } else if (sub == 1) {
                    idx1 = -1 - BITS_READ(ipp, &ibo, 8);
                    idx2 = -1 - BITS_READ(ipp, &ibo, 8);
                    val1 = opp[idx1];
                    val2 = opp[idx1];
                    val = (val1 & 0xfffff000) | (val2 & 0x00000fff);
                } else if (sub == 2) {
                    idx1 = -1 - BITS_READ(ipp, &ibo, 8);
                    val1 = opp[idx1];
                    val2 = BITS_READ(ipp, &ibo, 8);
                    val3 = BITS_READ(ipp, &ibo, 4);
                    val = (val1 & 0xf00ffff0) | (val2 << 20) | val3;
                } else if (sub == 3) {
                    idx1 = BITS_READ(ipp, &ibo, 8);
                    if (idx1 == 2) {
                        // XXX: does this mean continue?
                        break;
                    }
                    if (idx1 == 1) {
                        eos = 1;
                        break;
                    }
                    idx1 = -1 - idx1;
                    val1 = opp[idx1];
                    val2 = BITS_READ(ipp, &ibo, 16);
                    val = 0;
                    val |= (val1 & 0x00ec3cfd);
                    val |= (0x00000002 & (val2 << 1));
                    val |= (0x00000300 & (val2 << 7));
                    val |= (0x0003c000 & (val2 << 11));
                    val |= (0x00100000 & (val2 << 13));
                    val |= (0xff000000 & (val2 << 16));
                }
                break;
            }
            default: {
                err = 1;
                fprintf(stderr, "%s:%d\n", __func__, __LINE__);
                break;
            }
            }
        }
        //
        if (err != 0)
            break;
        if (eos != 0)
            break;
        *opp++ = val;
    }

    return err ? -1 : 0;
}

int main(int argc, char *argv[]) {
    char opt;
    char *fi = NULL, *fo = NULL;
    unsigned long base = 0;
    int version = 16;
    int rc, n, nb, fdc, fdu;
    struct stat fs;
    void *comped;
    struct zip20_seg_hdr *zip20;
    struct zip16_seg_hdr *zip16;
    struct zip8_seg_hdr *zip8;
    void *uncomp;
    uint32_t i;

    while ((opt = getopt(argc, argv, "v:b:i:o:")) != -1) {
        switch (opt) {
        case 'b': {
            base = strtoul(optarg, NULL, 16);
            break;
        }
        case 'i': {
            fi = optarg;
            break;
        }
        case 'o': {
            fo = optarg;
            break;
        }
        case 'v': {
            version = atoi(optarg);
            break;
        }
        default: {
fail_usage:
            fprintf(stderr, "Usage: %s [-v version] -i <ifile> -o <ofile> -b <base>\n", argv[0]);
            return 1;
        }
        }
    }
    if (fi == NULL || fo == NULL ||
        (version != 8 && version != 16 && version != 20)) {
        goto fail_usage;
    }
    fdc = open(fi, O_RDONLY);
    if (fdc < 0) {
        perror("open");
        exit(1);
    }
    rc = fstat(fdc, &fs);
    if (rc) {
        perror("stat");
        exit(1);
    }
    comped = mmap(NULL, fs.st_size, PROT_READ, MAP_PRIVATE, fdc, 0);
    if (comped == MAP_FAILED) {
        perror("mmap");
        exit(1);
    }
    zip20 = (struct zip20_seg_hdr *) comped;
    zip16 = (struct zip16_seg_hdr *) comped;
    zip8 = (struct zip8_seg_hdr *) comped;
    if (version == 20) {
        nb = zip20->nb;
    } else if (version == 16) {
        nb = zip16->nb;
    } else {
        nb = zip8->nb;
    }
    nb = nb * BLOCK_SIZE * sizeof(uint32_t);
    uncomp = malloc(nb);
    if (uncomp == NULL) {
        perror("malloc");
        exit(1);
    }
    if (version == 20) {
        for (i = 0; i < zip20->nb; i++) {
            rc = uncompress_20(&zip20->dict[0], &zip20->dict[ZIP20_DICT1_SIZE], comped + zip20->va[i] - base, uncomp + i * BLOCK_SIZE * sizeof(uint32_t));
            if (rc) {
                fprintf(stderr, "error uncompress 0x%x\n", zip20->va[i]);
                break;
            }
        }
    } else if (version == 16) {
        for (i = 0; i < zip16->nb; i++) {
            rc = uncompress_16(&zip16->dict[0], &zip16->dict[ZIP16_DICT1_SIZE], comped + zip16->va[i] - base, uncomp + i * BLOCK_SIZE * sizeof(uint32_t));
            if (rc) {
                fprintf(stderr, "error uncompress 0x%x\n", zip16->va[i]);
                break;
            }
        }
    } else {
        for (i = 0; i < zip8->nb; i++) {
            rc = uncompress_8(&zip8->dict[0], comped + zip8->va[i] - base, uncomp + i * BLOCK_SIZE * sizeof(uint32_t));
            if (rc) {
                fprintf(stderr, "error uncompress 0x%x\n", zip8->va[i]);
                break;
            }
        }
    }
    fdu = open(fo, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fdu < 0) {
        perror("open");
        exit(1);
    }
    n = write(fdu, uncomp, nb);
    if (n != nb) {
        perror("write");
        exit(1);
    }
    close(fdu);
    free(uncomp);
    munmap(comped, fs.st_size);
    close(fdc);

    return 0;
}

