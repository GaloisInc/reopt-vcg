def vdppd1 : instruction :=
  definst "vdppd" $ do
    pattern fun (v_3477 : imm int) (v_3479 : reg (bv 128)) (v_3480 : reg (bv 128)) (v_3481 : reg (bv 128)) => do
      v_6536 <- eval (handleImmediateWithSignExtend v_3477 8 8);
      v_6539 <- getRegister v_3480;
      v_6542 <- getRegister v_3479;
      v_6559 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_6536 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6539 64 128) 53 11) (MInt2Float (extract v_6542 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (isBitSet v_6536 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6539 0 64) 53 11) (MInt2Float (extract v_6542 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_3481) (concat (mux (isBitSet v_6536 6) v_6559 (expression.bv_nat 64 0)) (mux (isBitSet v_6536 7) v_6559 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3471 : imm int) (v_3472 : Mem) (v_3473 : reg (bv 128)) (v_3474 : reg (bv 128)) => do
      v_10521 <- eval (handleImmediateWithSignExtend v_3471 8 8);
      v_10524 <- getRegister v_3473;
      v_10527 <- evaluateAddress v_3472;
      v_10528 <- load v_10527 16;
      v_10545 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_10521 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10524 64 128) 53 11) (MInt2Float (extract v_10528 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (isBitSet v_10521 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10524 0 64) 53 11) (MInt2Float (extract v_10528 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_3474) (concat (mux (isBitSet v_10521 6) v_10545 (expression.bv_nat 64 0)) (mux (isBitSet v_10521 7) v_10545 (expression.bv_nat 64 0)));
      pure ()
    pat_end
