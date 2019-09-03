def pshufhw1 : instruction :=
  definst "pshufhw" $ do
    pattern fun (v_2913 : imm int) (v_2911 : reg (bv 128)) (v_2912 : reg (bv 128)) => do
      v_7334 <- getRegister v_2911;
      v_7335 <- eval (handleImmediateWithSignExtend v_2913 8 8);
      v_7337 <- eval (concat (expression.bv_nat 126 0) (extract v_7335 0 2));
      v_7345 <- eval (concat (expression.bv_nat 126 0) (extract v_7335 2 4));
      v_7353 <- eval (concat (expression.bv_nat 126 0) (extract v_7335 4 6));
      v_7361 <- eval (concat (expression.bv_nat 126 0) (extract v_7335 6 8));
      setRegister (lhs.of_reg v_2912) (concat (extract (lshr v_7334 (uvalueMInt (extract (shl v_7337 4) 0 (bitwidthMInt v_7337)))) 48 64) (concat (extract (lshr v_7334 (uvalueMInt (extract (shl v_7345 4) 0 (bitwidthMInt v_7345)))) 48 64) (concat (extract (lshr v_7334 (uvalueMInt (extract (shl v_7353 4) 0 (bitwidthMInt v_7353)))) 48 64) (concat (extract (lshr v_7334 (uvalueMInt (extract (shl v_7361 4) 0 (bitwidthMInt v_7361)))) 48 64) (extract v_7334 64 128)))));
      pure ()
    pat_end;
    pattern fun (v_2907 : imm int) (v_2905 : Mem) (v_2906 : reg (bv 128)) => do
      v_14553 <- evaluateAddress v_2905;
      v_14554 <- load v_14553 16;
      v_14555 <- eval (handleImmediateWithSignExtend v_2907 8 8);
      v_14557 <- eval (concat (expression.bv_nat 126 0) (extract v_14555 0 2));
      v_14565 <- eval (concat (expression.bv_nat 126 0) (extract v_14555 2 4));
      v_14573 <- eval (concat (expression.bv_nat 126 0) (extract v_14555 4 6));
      v_14581 <- eval (concat (expression.bv_nat 126 0) (extract v_14555 6 8));
      setRegister (lhs.of_reg v_2906) (concat (extract (lshr v_14554 (uvalueMInt (extract (shl v_14557 4) 0 (bitwidthMInt v_14557)))) 48 64) (concat (extract (lshr v_14554 (uvalueMInt (extract (shl v_14565 4) 0 (bitwidthMInt v_14565)))) 48 64) (concat (extract (lshr v_14554 (uvalueMInt (extract (shl v_14573 4) 0 (bitwidthMInt v_14573)))) 48 64) (concat (extract (lshr v_14554 (uvalueMInt (extract (shl v_14581 4) 0 (bitwidthMInt v_14581)))) 48 64) (extract v_14554 64 128)))));
      pure ()
    pat_end
