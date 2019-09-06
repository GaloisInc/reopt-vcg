def vfmsub213pd1 : instruction :=
  definst "vfmsub213pd" $ do
    pattern fun (v_2903 : reg (bv 128)) (v_2904 : reg (bv 128)) (v_2905 : reg (bv 128)) => do
      v_5740 <- getRegister v_2904;
      v_5743 <- getRegister v_2905;
      v_5747 <- getRegister v_2903;
      v_5751 <- eval (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5740 0 64) 53 11) (MInt2Float (extract v_5743 0 64) 53 11)) (MInt2Float (extract v_5747 0 64) 53 11)) 64);
      setRegister (lhs.of_reg v_2905) (concat (concat (extract v_5751 0 56) (extract v_5751 56 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5740 64 128) 53 11) (MInt2Float (extract v_5743 64 128) 53 11)) (MInt2Float (extract v_5747 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2917 : reg (bv 256)) (v_2918 : reg (bv 256)) (v_2919 : reg (bv 256)) => do
      v_5771 <- getRegister v_2918;
      v_5774 <- getRegister v_2919;
      v_5778 <- getRegister v_2917;
      setRegister (lhs.of_reg v_2919) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5771 0 64) 53 11) (MInt2Float (extract v_5774 0 64) 53 11)) (MInt2Float (extract v_5778 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5771 64 128) 53 11) (MInt2Float (extract v_5774 64 128) 53 11)) (MInt2Float (extract v_5778 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5771 128 192) 53 11) (MInt2Float (extract v_5774 128 192) 53 11)) (MInt2Float (extract v_5778 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5771 192 256) 53 11) (MInt2Float (extract v_5774 192 256) 53 11)) (MInt2Float (extract v_5778 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_2900 : Mem) (v_2898 : reg (bv 128)) (v_2899 : reg (bv 128)) => do
      v_11622 <- getRegister v_2898;
      v_11625 <- getRegister v_2899;
      v_11629 <- evaluateAddress v_2900;
      v_11630 <- load v_11629 16;
      v_11634 <- eval (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11622 0 64) 53 11) (MInt2Float (extract v_11625 0 64) 53 11)) (MInt2Float (extract v_11630 0 64) 53 11)) 64);
      setRegister (lhs.of_reg v_2899) (concat (concat (extract v_11634 0 56) (extract v_11634 56 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11622 64 128) 53 11) (MInt2Float (extract v_11625 64 128) 53 11)) (MInt2Float (extract v_11630 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2909 : Mem) (v_2912 : reg (bv 256)) (v_2913 : reg (bv 256)) => do
      v_11649 <- getRegister v_2912;
      v_11652 <- getRegister v_2913;
      v_11656 <- evaluateAddress v_2909;
      v_11657 <- load v_11656 32;
      setRegister (lhs.of_reg v_2913) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11649 0 64) 53 11) (MInt2Float (extract v_11652 0 64) 53 11)) (MInt2Float (extract v_11657 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11649 64 128) 53 11) (MInt2Float (extract v_11652 64 128) 53 11)) (MInt2Float (extract v_11657 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11649 128 192) 53 11) (MInt2Float (extract v_11652 128 192) 53 11)) (MInt2Float (extract v_11657 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11649 192 256) 53 11) (MInt2Float (extract v_11652 192 256) 53 11)) (MInt2Float (extract v_11657 192 256) 53 11)) 64))));
      pure ()
    pat_end
