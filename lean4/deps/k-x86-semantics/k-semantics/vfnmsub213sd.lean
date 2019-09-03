def vfnmsub213sd1 : instruction :=
  definst "vfnmsub213sd" $ do
    pattern fun (v_3399 : reg (bv 128)) (v_3400 : reg (bv 128)) (v_3401 : reg (bv 128)) => do
      v_12219 <- getRegister v_3401;
      v_12221 <- getRegister v_3400;
      v_12222 <- eval (extract v_12221 64 128);
      v_12230 <- eval (extract v_12219 64 128);
      v_12240 <- getRegister v_3399;
      v_12241 <- eval (extract v_12240 64 128);
      setRegister (lhs.of_reg v_3401) (concat (extract v_12219 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12222 0 1)) (uvalueMInt (extract v_12222 1 12)) (uvalueMInt (extract v_12222 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12230 0 1)) (uvalueMInt (extract v_12230 1 12)) (uvalueMInt (extract v_12230 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12241 0 1)) (uvalueMInt (extract v_12241 1 12)) (uvalueMInt (extract v_12241 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3396 : Mem) (v_3394 : reg (bv 128)) (v_3395 : reg (bv 128)) => do
      v_22796 <- getRegister v_3395;
      v_22798 <- getRegister v_3394;
      v_22799 <- eval (extract v_22798 64 128);
      v_22807 <- eval (extract v_22796 64 128);
      v_22817 <- evaluateAddress v_3396;
      v_22818 <- load v_22817 8;
      setRegister (lhs.of_reg v_3395) (concat (extract v_22796 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22799 0 1)) (uvalueMInt (extract v_22799 1 12)) (uvalueMInt (extract v_22799 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22807 0 1)) (uvalueMInt (extract v_22807 1 12)) (uvalueMInt (extract v_22807 12 64))))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_22818 0 1)) (uvalueMInt (extract v_22818 1 12)) (uvalueMInt (extract v_22818 12 64)))) 64));
      pure ()
    pat_end
