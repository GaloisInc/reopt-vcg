def vfmsub132pd1 : instruction :=
  definst "vfmsub132pd" $ do
    pattern fun (v_2813 : reg (bv 128)) (v_2814 : reg (bv 128)) (v_2815 : reg (bv 128)) => do
      v_5461 <- getRegister v_2815;
      v_5464 <- getRegister v_2813;
      v_5468 <- getRegister v_2814;
      setRegister (lhs.of_reg v_2815) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5461 0 64) 53 11) (MInt2Float (extract v_5464 0 64) 53 11)) (MInt2Float (extract v_5468 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5461 64 128) 53 11) (MInt2Float (extract v_5464 64 128) 53 11)) (MInt2Float (extract v_5468 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2823 : reg (bv 256)) (v_2824 : reg (bv 256)) (v_2825 : reg (bv 256)) => do
      v_5489 <- getRegister v_2825;
      v_5492 <- getRegister v_2823;
      v_5496 <- getRegister v_2824;
      setRegister (lhs.of_reg v_2825) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5489 0 64) 53 11) (MInt2Float (extract v_5492 0 64) 53 11)) (MInt2Float (extract v_5496 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5489 64 128) 53 11) (MInt2Float (extract v_5492 64 128) 53 11)) (MInt2Float (extract v_5496 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5489 128 192) 53 11) (MInt2Float (extract v_5492 128 192) 53 11)) (MInt2Float (extract v_5496 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5489 192 256) 53 11) (MInt2Float (extract v_5492 192 256) 53 11)) (MInt2Float (extract v_5496 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_2807 : Mem) (v_2808 : reg (bv 128)) (v_2809 : reg (bv 128)) => do
      v_11369 <- getRegister v_2809;
      v_11372 <- evaluateAddress v_2807;
      v_11373 <- load v_11372 16;
      v_11377 <- getRegister v_2808;
      setRegister (lhs.of_reg v_2809) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11369 0 64) 53 11) (MInt2Float (extract v_11373 0 64) 53 11)) (MInt2Float (extract v_11377 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11369 64 128) 53 11) (MInt2Float (extract v_11373 64 128) 53 11)) (MInt2Float (extract v_11377 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2818 : Mem) (v_2819 : reg (bv 256)) (v_2820 : reg (bv 256)) => do
      v_11393 <- getRegister v_2820;
      v_11396 <- evaluateAddress v_2818;
      v_11397 <- load v_11396 32;
      v_11401 <- getRegister v_2819;
      setRegister (lhs.of_reg v_2820) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11393 0 64) 53 11) (MInt2Float (extract v_11397 0 64) 53 11)) (MInt2Float (extract v_11401 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11393 64 128) 53 11) (MInt2Float (extract v_11397 64 128) 53 11)) (MInt2Float (extract v_11401 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11393 128 192) 53 11) (MInt2Float (extract v_11397 128 192) 53 11)) (MInt2Float (extract v_11401 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11393 192 256) 53 11) (MInt2Float (extract v_11397 192 256) 53 11)) (MInt2Float (extract v_11401 192 256) 53 11)) 64))));
      pure ()
    pat_end
