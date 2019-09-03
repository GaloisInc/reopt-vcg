def vdppd1 : instruction :=
  definst "vdppd" $ do
    pattern fun (v_3424 : imm int) (v_3428 : reg (bv 128)) (v_3429 : reg (bv 128)) (v_3430 : reg (bv 128)) => do
      v_7541 <- eval (handleImmediateWithSignExtend v_3424 8 8);
      v_7546 <- getRegister v_3429;
      v_7547 <- eval (extract v_7546 64 128);
      v_7555 <- getRegister v_3428;
      v_7556 <- eval (extract v_7555 64 128);
      v_7570 <- eval (extract v_7546 0 64);
      v_7578 <- eval (extract v_7555 0 64);
      v_7591 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_7541 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7547 0 1)) (uvalueMInt (extract v_7547 1 12)) (uvalueMInt (extract v_7547 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7556 0 1)) (uvalueMInt (extract v_7556 1 12)) (uvalueMInt (extract v_7556 12 64)))) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (eq (extract v_7541 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7570 0 1)) (uvalueMInt (extract v_7570 1 12)) (uvalueMInt (extract v_7570 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7578 0 1)) (uvalueMInt (extract v_7578 1 12)) (uvalueMInt (extract v_7578 12 64)))) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_3430) (concat (mux (eq (extract v_7541 6 7) (expression.bv_nat 1 1)) v_7591 (expression.bv_nat 64 0)) (mux (eq (extract v_7541 7 8) (expression.bv_nat 1 1)) v_7591 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3419 : imm int) (v_3418 : Mem) (v_3422 : reg (bv 128)) (v_3423 : reg (bv 128)) => do
      v_12733 <- eval (handleImmediateWithSignExtend v_3419 8 8);
      v_12738 <- getRegister v_3422;
      v_12739 <- eval (extract v_12738 64 128);
      v_12747 <- evaluateAddress v_3418;
      v_12748 <- load v_12747 16;
      v_12749 <- eval (extract v_12748 64 128);
      v_12763 <- eval (extract v_12738 0 64);
      v_12771 <- eval (extract v_12748 0 64);
      v_12784 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_12733 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12739 0 1)) (uvalueMInt (extract v_12739 1 12)) (uvalueMInt (extract v_12739 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12749 0 1)) (uvalueMInt (extract v_12749 1 12)) (uvalueMInt (extract v_12749 12 64)))) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (eq (extract v_12733 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12763 0 1)) (uvalueMInt (extract v_12763 1 12)) (uvalueMInt (extract v_12763 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12771 0 1)) (uvalueMInt (extract v_12771 1 12)) (uvalueMInt (extract v_12771 12 64)))) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_3423) (concat (mux (eq (extract v_12733 6 7) (expression.bv_nat 1 1)) v_12784 (expression.bv_nat 64 0)) (mux (eq (extract v_12733 7 8) (expression.bv_nat 1 1)) v_12784 (expression.bv_nat 64 0)));
      pure ()
    pat_end
