def vdivsd1 : instruction :=
  definst "vdivsd" $ do
    pattern fun (v_3404 : reg (bv 128)) (v_3405 : reg (bv 128)) (v_3406 : reg (bv 128)) => do
      v_7484 <- getRegister v_3405;
      v_7486 <- eval (extract v_7484 64 128);
      v_7494 <- getRegister v_3404;
      v_7495 <- eval (extract v_7494 64 128);
      setRegister (lhs.of_reg v_3406) (concat (extract v_7484 0 64) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7486 0 1)) (uvalueMInt (extract v_7486 1 12)) (uvalueMInt (extract v_7486 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7495 0 1)) (uvalueMInt (extract v_7495 1 12)) (uvalueMInt (extract v_7495 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3396 : Mem) (v_3399 : reg (bv 128)) (v_3400 : reg (bv 128)) => do
      v_12687 <- getRegister v_3399;
      v_12689 <- eval (extract v_12687 64 128);
      v_12697 <- evaluateAddress v_3396;
      v_12698 <- load v_12697 8;
      setRegister (lhs.of_reg v_3400) (concat (extract v_12687 0 64) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12689 0 1)) (uvalueMInt (extract v_12689 1 12)) (uvalueMInt (extract v_12689 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12698 0 1)) (uvalueMInt (extract v_12698 1 12)) (uvalueMInt (extract v_12698 12 64)))) 64));
      pure ()
    pat_end
