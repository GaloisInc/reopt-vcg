def vfmsub213pd1 : instruction :=
  definst "vfmsub213pd" $ do
    pattern fun (v_2879 : reg (bv 128)) (v_2880 : reg (bv 128)) (v_2881 : reg (bv 128)) => do
      v_5713 <- getRegister v_2880;
      v_5716 <- getRegister v_2881;
      v_5720 <- getRegister v_2879;
      v_5724 <- eval (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5713 0 64) 53 11) (MInt2Float (extract v_5716 0 64) 53 11)) (MInt2Float (extract v_5720 0 64) 53 11)) 64);
      setRegister (lhs.of_reg v_2881) (concat (concat (extract v_5724 0 56) (extract v_5724 56 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5713 64 128) 53 11) (MInt2Float (extract v_5716 64 128) 53 11)) (MInt2Float (extract v_5720 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2889 : reg (bv 256)) (v_2890 : reg (bv 256)) (v_2891 : reg (bv 256)) => do
      v_5744 <- getRegister v_2890;
      v_5747 <- getRegister v_2891;
      v_5751 <- getRegister v_2889;
      setRegister (lhs.of_reg v_2891) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5744 0 64) 53 11) (MInt2Float (extract v_5747 0 64) 53 11)) (MInt2Float (extract v_5751 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5744 64 128) 53 11) (MInt2Float (extract v_5747 64 128) 53 11)) (MInt2Float (extract v_5751 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5744 128 192) 53 11) (MInt2Float (extract v_5747 128 192) 53 11)) (MInt2Float (extract v_5751 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5744 192 256) 53 11) (MInt2Float (extract v_5747 192 256) 53 11)) (MInt2Float (extract v_5751 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_2873 : Mem) (v_2874 : reg (bv 128)) (v_2875 : reg (bv 128)) => do
      v_11595 <- getRegister v_2874;
      v_11598 <- getRegister v_2875;
      v_11602 <- evaluateAddress v_2873;
      v_11603 <- load v_11602 16;
      v_11607 <- eval (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11595 0 64) 53 11) (MInt2Float (extract v_11598 0 64) 53 11)) (MInt2Float (extract v_11603 0 64) 53 11)) 64);
      setRegister (lhs.of_reg v_2875) (concat (concat (extract v_11607 0 56) (extract v_11607 56 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11595 64 128) 53 11) (MInt2Float (extract v_11598 64 128) 53 11)) (MInt2Float (extract v_11603 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2884 : Mem) (v_2885 : reg (bv 256)) (v_2886 : reg (bv 256)) => do
      v_11622 <- getRegister v_2885;
      v_11625 <- getRegister v_2886;
      v_11629 <- evaluateAddress v_2884;
      v_11630 <- load v_11629 32;
      setRegister (lhs.of_reg v_2886) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11622 0 64) 53 11) (MInt2Float (extract v_11625 0 64) 53 11)) (MInt2Float (extract v_11630 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11622 64 128) 53 11) (MInt2Float (extract v_11625 64 128) 53 11)) (MInt2Float (extract v_11630 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11622 128 192) 53 11) (MInt2Float (extract v_11625 128 192) 53 11)) (MInt2Float (extract v_11630 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11622 192 256) 53 11) (MInt2Float (extract v_11625 192 256) 53 11)) (MInt2Float (extract v_11630 192 256) 53 11)) 64))));
      pure ()
    pat_end
