def vfmaddsub213pd1 : instruction :=
  definst "vfmaddsub213pd" $ do
    pattern fun (v_2673 : reg (bv 128)) (v_2674 : reg (bv 128)) (v_2675 : reg (bv 128)) => do
      v_6098 <- getRegister v_2674;
      v_6099 <- eval (extract v_6098 0 64);
      v_6107 <- getRegister v_2675;
      v_6108 <- eval (extract v_6107 0 64);
      v_6117 <- getRegister v_2673;
      v_6118 <- eval (extract v_6117 0 64);
      v_6128 <- eval (extract v_6098 64 128);
      v_6136 <- eval (extract v_6107 64 128);
      v_6145 <- eval (extract v_6117 64 128);
      setRegister (lhs.of_reg v_2675) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6099 0 1)) (uvalueMInt (extract v_6099 1 12)) (uvalueMInt (extract v_6099 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6108 0 1)) (uvalueMInt (extract v_6108 1 12)) (uvalueMInt (extract v_6108 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6118 0 1)) (uvalueMInt (extract v_6118 1 12)) (uvalueMInt (extract v_6118 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6128 0 1)) (uvalueMInt (extract v_6128 1 12)) (uvalueMInt (extract v_6128 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6136 0 1)) (uvalueMInt (extract v_6136 1 12)) (uvalueMInt (extract v_6136 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6145 0 1)) (uvalueMInt (extract v_6145 1 12)) (uvalueMInt (extract v_6145 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2684 : reg (bv 256)) (v_2685 : reg (bv 256)) (v_2686 : reg (bv 256)) => do
      v_6162 <- getRegister v_2685;
      v_6163 <- eval (extract v_6162 0 64);
      v_6171 <- getRegister v_2686;
      v_6172 <- eval (extract v_6171 0 64);
      v_6181 <- getRegister v_2684;
      v_6182 <- eval (extract v_6181 0 64);
      v_6192 <- eval (extract v_6162 64 128);
      v_6200 <- eval (extract v_6171 64 128);
      v_6209 <- eval (extract v_6181 64 128);
      v_6220 <- eval (extract v_6162 128 192);
      v_6228 <- eval (extract v_6171 128 192);
      v_6237 <- eval (extract v_6181 128 192);
      v_6247 <- eval (extract v_6162 192 256);
      v_6255 <- eval (extract v_6171 192 256);
      v_6264 <- eval (extract v_6181 192 256);
      setRegister (lhs.of_reg v_2686) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6163 0 1)) (uvalueMInt (extract v_6163 1 12)) (uvalueMInt (extract v_6163 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6172 0 1)) (uvalueMInt (extract v_6172 1 12)) (uvalueMInt (extract v_6172 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6182 0 1)) (uvalueMInt (extract v_6182 1 12)) (uvalueMInt (extract v_6182 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6192 0 1)) (uvalueMInt (extract v_6192 1 12)) (uvalueMInt (extract v_6192 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6200 0 1)) (uvalueMInt (extract v_6200 1 12)) (uvalueMInt (extract v_6200 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6209 0 1)) (uvalueMInt (extract v_6209 1 12)) (uvalueMInt (extract v_6209 12 64)))) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6220 0 1)) (uvalueMInt (extract v_6220 1 12)) (uvalueMInt (extract v_6220 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6228 0 1)) (uvalueMInt (extract v_6228 1 12)) (uvalueMInt (extract v_6228 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6237 0 1)) (uvalueMInt (extract v_6237 1 12)) (uvalueMInt (extract v_6237 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6247 0 1)) (uvalueMInt (extract v_6247 1 12)) (uvalueMInt (extract v_6247 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6255 0 1)) (uvalueMInt (extract v_6255 1 12)) (uvalueMInt (extract v_6255 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6264 0 1)) (uvalueMInt (extract v_6264 1 12)) (uvalueMInt (extract v_6264 12 64)))) 64)));
      pure ()
    pat_end;
    pattern fun (v_2670 : Mem) (v_2668 : reg (bv 128)) (v_2669 : reg (bv 128)) => do
      v_16953 <- getRegister v_2668;
      v_16954 <- eval (extract v_16953 0 64);
      v_16962 <- getRegister v_2669;
      v_16963 <- eval (extract v_16962 0 64);
      v_16972 <- evaluateAddress v_2670;
      v_16973 <- load v_16972 16;
      v_16974 <- eval (extract v_16973 0 64);
      v_16984 <- eval (extract v_16953 64 128);
      v_16992 <- eval (extract v_16962 64 128);
      v_17001 <- eval (extract v_16973 64 128);
      setRegister (lhs.of_reg v_2669) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16954 0 1)) (uvalueMInt (extract v_16954 1 12)) (uvalueMInt (extract v_16954 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16963 0 1)) (uvalueMInt (extract v_16963 1 12)) (uvalueMInt (extract v_16963 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16974 0 1)) (uvalueMInt (extract v_16974 1 12)) (uvalueMInt (extract v_16974 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16984 0 1)) (uvalueMInt (extract v_16984 1 12)) (uvalueMInt (extract v_16984 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_16992 0 1)) (uvalueMInt (extract v_16992 1 12)) (uvalueMInt (extract v_16992 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17001 0 1)) (uvalueMInt (extract v_17001 1 12)) (uvalueMInt (extract v_17001 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2679 : Mem) (v_2680 : reg (bv 256)) (v_2681 : reg (bv 256)) => do
      v_17013 <- getRegister v_2680;
      v_17014 <- eval (extract v_17013 0 64);
      v_17022 <- getRegister v_2681;
      v_17023 <- eval (extract v_17022 0 64);
      v_17032 <- evaluateAddress v_2679;
      v_17033 <- load v_17032 32;
      v_17034 <- eval (extract v_17033 0 64);
      v_17044 <- eval (extract v_17013 64 128);
      v_17052 <- eval (extract v_17022 64 128);
      v_17061 <- eval (extract v_17033 64 128);
      v_17072 <- eval (extract v_17013 128 192);
      v_17080 <- eval (extract v_17022 128 192);
      v_17089 <- eval (extract v_17033 128 192);
      v_17099 <- eval (extract v_17013 192 256);
      v_17107 <- eval (extract v_17022 192 256);
      v_17116 <- eval (extract v_17033 192 256);
      setRegister (lhs.of_reg v_2681) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17014 0 1)) (uvalueMInt (extract v_17014 1 12)) (uvalueMInt (extract v_17014 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17023 0 1)) (uvalueMInt (extract v_17023 1 12)) (uvalueMInt (extract v_17023 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17034 0 1)) (uvalueMInt (extract v_17034 1 12)) (uvalueMInt (extract v_17034 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17044 0 1)) (uvalueMInt (extract v_17044 1 12)) (uvalueMInt (extract v_17044 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17052 0 1)) (uvalueMInt (extract v_17052 1 12)) (uvalueMInt (extract v_17052 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17061 0 1)) (uvalueMInt (extract v_17061 1 12)) (uvalueMInt (extract v_17061 12 64)))) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17072 0 1)) (uvalueMInt (extract v_17072 1 12)) (uvalueMInt (extract v_17072 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17080 0 1)) (uvalueMInt (extract v_17080 1 12)) (uvalueMInt (extract v_17080 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17089 0 1)) (uvalueMInt (extract v_17089 1 12)) (uvalueMInt (extract v_17089 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17099 0 1)) (uvalueMInt (extract v_17099 1 12)) (uvalueMInt (extract v_17099 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17107 0 1)) (uvalueMInt (extract v_17107 1 12)) (uvalueMInt (extract v_17107 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17116 0 1)) (uvalueMInt (extract v_17116 1 12)) (uvalueMInt (extract v_17116 12 64)))) 64)));
      pure ()
    pat_end
