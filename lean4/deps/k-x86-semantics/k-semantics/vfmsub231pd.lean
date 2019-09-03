def vfmsub231pd1 : instruction :=
  definst "vfmsub231pd" $ do
    pattern fun (v_2880 : reg (bv 128)) (v_2881 : reg (bv 128)) (v_2882 : reg (bv 128)) => do
      v_5901 <- getRegister v_2881;
      v_5904 <- getRegister v_2880;
      v_5908 <- getRegister v_2882;
      setRegister (lhs.of_reg v_2882) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5901 0 64) 53 11) (MInt2Float (extract v_5904 0 64) 53 11)) (MInt2Float (extract v_5908 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5901 64 128) 53 11) (MInt2Float (extract v_5904 64 128) 53 11)) (MInt2Float (extract v_5908 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2892 : reg (bv 256)) (v_2893 : reg (bv 256)) (v_2894 : reg (bv 256)) => do
      v_5929 <- getRegister v_2893;
      v_5932 <- getRegister v_2892;
      v_5936 <- getRegister v_2894;
      setRegister (lhs.of_reg v_2894) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5929 0 64) 53 11) (MInt2Float (extract v_5932 0 64) 53 11)) (MInt2Float (extract v_5936 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5929 64 128) 53 11) (MInt2Float (extract v_5932 64 128) 53 11)) (MInt2Float (extract v_5936 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5929 128 192) 53 11) (MInt2Float (extract v_5932 128 192) 53 11)) (MInt2Float (extract v_5936 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5929 192 256) 53 11) (MInt2Float (extract v_5932 192 256) 53 11)) (MInt2Float (extract v_5936 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2877 : Mem) (v_2875 : reg (bv 128)) (v_2876 : reg (bv 128)) => do
      v_11740 <- getRegister v_2875;
      v_11743 <- evaluateAddress v_2877;
      v_11744 <- load v_11743 16;
      v_11748 <- getRegister v_2876;
      setRegister (lhs.of_reg v_2876) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11740 0 64) 53 11) (MInt2Float (extract v_11744 0 64) 53 11)) (MInt2Float (extract v_11748 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11740 64 128) 53 11) (MInt2Float (extract v_11744 64 128) 53 11)) (MInt2Float (extract v_11748 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2886 : Mem) (v_2887 : reg (bv 256)) (v_2888 : reg (bv 256)) => do
      v_11764 <- getRegister v_2887;
      v_11767 <- evaluateAddress v_2886;
      v_11768 <- load v_11767 32;
      v_11772 <- getRegister v_2888;
      setRegister (lhs.of_reg v_2888) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11764 0 64) 53 11) (MInt2Float (extract v_11768 0 64) 53 11)) (MInt2Float (extract v_11772 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11764 64 128) 53 11) (MInt2Float (extract v_11768 64 128) 53 11)) (MInt2Float (extract v_11772 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11764 128 192) 53 11) (MInt2Float (extract v_11768 128 192) 53 11)) (MInt2Float (extract v_11772 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11764 192 256) 53 11) (MInt2Float (extract v_11768 192 256) 53 11)) (MInt2Float (extract v_11772 192 256) 53 11)) 64)));
      pure ()
    pat_end
