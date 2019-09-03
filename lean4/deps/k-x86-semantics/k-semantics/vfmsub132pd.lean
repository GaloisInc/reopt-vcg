def vfmsub132pd1 : instruction :=
  definst "vfmsub132pd" $ do
    pattern fun (v_2761 : reg (bv 128)) (v_2762 : reg (bv 128)) (v_2763 : reg (bv 128)) => do
      v_7170 <- getRegister v_2763;
      v_7171 <- eval (extract v_7170 0 64);
      v_7179 <- getRegister v_2761;
      v_7180 <- eval (extract v_7179 0 64);
      v_7189 <- getRegister v_2762;
      v_7190 <- eval (extract v_7189 0 64);
      v_7200 <- eval (extract v_7170 64 128);
      v_7208 <- eval (extract v_7179 64 128);
      v_7217 <- eval (extract v_7189 64 128);
      setRegister (lhs.of_reg v_2763) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7171 0 1)) (uvalueMInt (extract v_7171 1 12)) (uvalueMInt (extract v_7171 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7180 0 1)) (uvalueMInt (extract v_7180 1 12)) (uvalueMInt (extract v_7180 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7190 0 1)) (uvalueMInt (extract v_7190 1 12)) (uvalueMInt (extract v_7190 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7200 0 1)) (uvalueMInt (extract v_7200 1 12)) (uvalueMInt (extract v_7200 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7208 0 1)) (uvalueMInt (extract v_7208 1 12)) (uvalueMInt (extract v_7208 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7217 0 1)) (uvalueMInt (extract v_7217 1 12)) (uvalueMInt (extract v_7217 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2772 : reg (bv 256)) (v_2773 : reg (bv 256)) (v_2774 : reg (bv 256)) => do
      v_7234 <- getRegister v_2774;
      v_7235 <- eval (extract v_7234 0 64);
      v_7243 <- getRegister v_2772;
      v_7244 <- eval (extract v_7243 0 64);
      v_7253 <- getRegister v_2773;
      v_7254 <- eval (extract v_7253 0 64);
      v_7264 <- eval (extract v_7234 64 128);
      v_7272 <- eval (extract v_7243 64 128);
      v_7281 <- eval (extract v_7253 64 128);
      v_7291 <- eval (extract v_7234 128 192);
      v_7299 <- eval (extract v_7243 128 192);
      v_7308 <- eval (extract v_7253 128 192);
      v_7318 <- eval (extract v_7234 192 256);
      v_7326 <- eval (extract v_7243 192 256);
      v_7335 <- eval (extract v_7253 192 256);
      setRegister (lhs.of_reg v_2774) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7235 0 1)) (uvalueMInt (extract v_7235 1 12)) (uvalueMInt (extract v_7235 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7244 0 1)) (uvalueMInt (extract v_7244 1 12)) (uvalueMInt (extract v_7244 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7254 0 1)) (uvalueMInt (extract v_7254 1 12)) (uvalueMInt (extract v_7254 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7264 0 1)) (uvalueMInt (extract v_7264 1 12)) (uvalueMInt (extract v_7264 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7272 0 1)) (uvalueMInt (extract v_7272 1 12)) (uvalueMInt (extract v_7272 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7281 0 1)) (uvalueMInt (extract v_7281 1 12)) (uvalueMInt (extract v_7281 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7291 0 1)) (uvalueMInt (extract v_7291 1 12)) (uvalueMInt (extract v_7291 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7299 0 1)) (uvalueMInt (extract v_7299 1 12)) (uvalueMInt (extract v_7299 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7308 0 1)) (uvalueMInt (extract v_7308 1 12)) (uvalueMInt (extract v_7308 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7318 0 1)) (uvalueMInt (extract v_7318 1 12)) (uvalueMInt (extract v_7318 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7326 0 1)) (uvalueMInt (extract v_7326 1 12)) (uvalueMInt (extract v_7326 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7335 0 1)) (uvalueMInt (extract v_7335 1 12)) (uvalueMInt (extract v_7335 12 64)))) 64))));
      pure ()
    pat_end;
    pattern fun (v_2758 : Mem) (v_2756 : reg (bv 128)) (v_2757 : reg (bv 128)) => do
      v_17993 <- getRegister v_2757;
      v_17994 <- eval (extract v_17993 0 64);
      v_18002 <- evaluateAddress v_2758;
      v_18003 <- load v_18002 16;
      v_18004 <- eval (extract v_18003 0 64);
      v_18013 <- getRegister v_2756;
      v_18014 <- eval (extract v_18013 0 64);
      v_18024 <- eval (extract v_17993 64 128);
      v_18032 <- eval (extract v_18003 64 128);
      v_18041 <- eval (extract v_18013 64 128);
      setRegister (lhs.of_reg v_2757) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17994 0 1)) (uvalueMInt (extract v_17994 1 12)) (uvalueMInt (extract v_17994 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18004 0 1)) (uvalueMInt (extract v_18004 1 12)) (uvalueMInt (extract v_18004 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18014 0 1)) (uvalueMInt (extract v_18014 1 12)) (uvalueMInt (extract v_18014 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18024 0 1)) (uvalueMInt (extract v_18024 1 12)) (uvalueMInt (extract v_18024 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18032 0 1)) (uvalueMInt (extract v_18032 1 12)) (uvalueMInt (extract v_18032 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18041 0 1)) (uvalueMInt (extract v_18041 1 12)) (uvalueMInt (extract v_18041 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2767 : Mem) (v_2768 : reg (bv 256)) (v_2769 : reg (bv 256)) => do
      v_18053 <- getRegister v_2769;
      v_18054 <- eval (extract v_18053 0 64);
      v_18062 <- evaluateAddress v_2767;
      v_18063 <- load v_18062 32;
      v_18064 <- eval (extract v_18063 0 64);
      v_18073 <- getRegister v_2768;
      v_18074 <- eval (extract v_18073 0 64);
      v_18084 <- eval (extract v_18053 64 128);
      v_18092 <- eval (extract v_18063 64 128);
      v_18101 <- eval (extract v_18073 64 128);
      v_18111 <- eval (extract v_18053 128 192);
      v_18119 <- eval (extract v_18063 128 192);
      v_18128 <- eval (extract v_18073 128 192);
      v_18138 <- eval (extract v_18053 192 256);
      v_18146 <- eval (extract v_18063 192 256);
      v_18155 <- eval (extract v_18073 192 256);
      setRegister (lhs.of_reg v_2769) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18054 0 1)) (uvalueMInt (extract v_18054 1 12)) (uvalueMInt (extract v_18054 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18064 0 1)) (uvalueMInt (extract v_18064 1 12)) (uvalueMInt (extract v_18064 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18074 0 1)) (uvalueMInt (extract v_18074 1 12)) (uvalueMInt (extract v_18074 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18084 0 1)) (uvalueMInt (extract v_18084 1 12)) (uvalueMInt (extract v_18084 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18092 0 1)) (uvalueMInt (extract v_18092 1 12)) (uvalueMInt (extract v_18092 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18101 0 1)) (uvalueMInt (extract v_18101 1 12)) (uvalueMInt (extract v_18101 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18111 0 1)) (uvalueMInt (extract v_18111 1 12)) (uvalueMInt (extract v_18111 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18119 0 1)) (uvalueMInt (extract v_18119 1 12)) (uvalueMInt (extract v_18119 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18128 0 1)) (uvalueMInt (extract v_18128 1 12)) (uvalueMInt (extract v_18128 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18138 0 1)) (uvalueMInt (extract v_18138 1 12)) (uvalueMInt (extract v_18138 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18146 0 1)) (uvalueMInt (extract v_18146 1 12)) (uvalueMInt (extract v_18146 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18155 0 1)) (uvalueMInt (extract v_18155 1 12)) (uvalueMInt (extract v_18155 12 64)))) 64))));
      pure ()
    pat_end
