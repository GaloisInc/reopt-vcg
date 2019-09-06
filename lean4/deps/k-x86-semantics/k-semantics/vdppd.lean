def vdppd1 : instruction :=
  definst "vdppd" $ do
    pattern fun (v_3502 : imm int) (v_3506 : reg (bv 128)) (v_3507 : reg (bv 128)) (v_3508 : reg (bv 128)) => do
      v_6563 <- eval (handleImmediateWithSignExtend v_3502 8 8);
      v_6566 <- getRegister v_3507;
      v_6569 <- getRegister v_3506;
      v_6586 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_6563 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6566 64 128) 53 11) (MInt2Float (extract v_6569 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (isBitSet v_6563 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6566 0 64) 53 11) (MInt2Float (extract v_6569 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_3508) (concat (mux (isBitSet v_6563 6) v_6586 (expression.bv_nat 64 0)) (mux (isBitSet v_6563 7) v_6586 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3496 : imm int) (v_3497 : Mem) (v_3500 : reg (bv 128)) (v_3501 : reg (bv 128)) => do
      v_10548 <- eval (handleImmediateWithSignExtend v_3496 8 8);
      v_10551 <- getRegister v_3500;
      v_10554 <- evaluateAddress v_3497;
      v_10555 <- load v_10554 16;
      v_10572 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_10548 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10551 64 128) 53 11) (MInt2Float (extract v_10555 64 128) 53 11)) 64) (expression.bv_nat 64 0)) 53 11) (MInt2Float (mux (isBitSet v_10548 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10551 0 64) 53 11) (MInt2Float (extract v_10555 0 64) 53 11)) 64) (expression.bv_nat 64 0)) 53 11)) 64);
      setRegister (lhs.of_reg v_3501) (concat (mux (isBitSet v_10548 6) v_10572 (expression.bv_nat 64 0)) (mux (isBitSet v_10548 7) v_10572 (expression.bv_nat 64 0)));
      pure ()
    pat_end
