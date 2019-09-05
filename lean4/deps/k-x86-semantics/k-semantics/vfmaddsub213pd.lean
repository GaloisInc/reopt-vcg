def vfmaddsub213pd1 : instruction :=
  definst "vfmaddsub213pd" $ do
    pattern fun (v_2725 : reg (bv 128)) (v_2726 : reg (bv 128)) (v_2727 : reg (bv 128)) => do
      v_5037 <- getRegister v_2726;
      v_5040 <- getRegister v_2727;
      v_5044 <- getRegister v_2725;
      setRegister (lhs.of_reg v_2727) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5037 0 64) 53 11) (MInt2Float (extract v_5040 0 64) 53 11)) (MInt2Float (extract v_5044 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5037 64 128) 53 11) (MInt2Float (extract v_5040 64 128) 53 11)) (MInt2Float (extract v_5044 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2735 : reg (bv 256)) (v_2736 : reg (bv 256)) (v_2737 : reg (bv 256)) => do
      v_5065 <- getRegister v_2736;
      v_5068 <- getRegister v_2737;
      v_5072 <- getRegister v_2735;
      setRegister (lhs.of_reg v_2737) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5065 0 64) 53 11) (MInt2Float (extract v_5068 0 64) 53 11)) (MInt2Float (extract v_5072 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5065 64 128) 53 11) (MInt2Float (extract v_5068 64 128) 53 11)) (MInt2Float (extract v_5072 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5065 128 192) 53 11) (MInt2Float (extract v_5068 128 192) 53 11)) (MInt2Float (extract v_5072 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5065 192 256) 53 11) (MInt2Float (extract v_5068 192 256) 53 11)) (MInt2Float (extract v_5072 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2719 : Mem) (v_2720 : reg (bv 128)) (v_2721 : reg (bv 128)) => do
      v_10977 <- getRegister v_2720;
      v_10980 <- getRegister v_2721;
      v_10984 <- evaluateAddress v_2719;
      v_10985 <- load v_10984 16;
      setRegister (lhs.of_reg v_2721) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10977 0 64) 53 11) (MInt2Float (extract v_10980 0 64) 53 11)) (MInt2Float (extract v_10985 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10977 64 128) 53 11) (MInt2Float (extract v_10980 64 128) 53 11)) (MInt2Float (extract v_10985 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2730 : Mem) (v_2731 : reg (bv 256)) (v_2732 : reg (bv 256)) => do
      v_11001 <- getRegister v_2731;
      v_11004 <- getRegister v_2732;
      v_11008 <- evaluateAddress v_2730;
      v_11009 <- load v_11008 32;
      setRegister (lhs.of_reg v_2732) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11001 0 64) 53 11) (MInt2Float (extract v_11004 0 64) 53 11)) (MInt2Float (extract v_11009 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11001 64 128) 53 11) (MInt2Float (extract v_11004 64 128) 53 11)) (MInt2Float (extract v_11009 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11001 128 192) 53 11) (MInt2Float (extract v_11004 128 192) 53 11)) (MInt2Float (extract v_11009 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11001 192 256) 53 11) (MInt2Float (extract v_11004 192 256) 53 11)) (MInt2Float (extract v_11009 192 256) 53 11)) 64)));
      pure ()
    pat_end
