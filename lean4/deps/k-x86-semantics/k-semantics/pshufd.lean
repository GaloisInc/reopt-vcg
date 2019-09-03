def pshufd1 : instruction :=
  definst "pshufd" $ do
    pattern fun (v_2902 : imm int) (v_2900 : reg (bv 128)) (v_2901 : reg (bv 128)) => do
      v_7291 <- getRegister v_2900;
      v_7292 <- eval (handleImmediateWithSignExtend v_2902 8 8);
      v_7294 <- eval (concat (expression.bv_nat 126 0) (extract v_7292 0 2));
      v_7302 <- eval (concat (expression.bv_nat 126 0) (extract v_7292 2 4));
      v_7310 <- eval (concat (expression.bv_nat 126 0) (extract v_7292 4 6));
      v_7318 <- eval (concat (expression.bv_nat 126 0) (extract v_7292 6 8));
      setRegister (lhs.of_reg v_2901) (concat (extract (lshr v_7291 (uvalueMInt (extract (shl v_7294 5) 0 (bitwidthMInt v_7294)))) 96 128) (concat (extract (lshr v_7291 (uvalueMInt (extract (shl v_7302 5) 0 (bitwidthMInt v_7302)))) 96 128) (concat (extract (lshr v_7291 (uvalueMInt (extract (shl v_7310 5) 0 (bitwidthMInt v_7310)))) 96 128) (extract (lshr v_7291 (uvalueMInt (extract (shl v_7318 5) 0 (bitwidthMInt v_7318)))) 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2896 : imm int) (v_2894 : Mem) (v_2895 : reg (bv 128)) => do
      v_14514 <- evaluateAddress v_2894;
      v_14515 <- load v_14514 16;
      v_14516 <- eval (handleImmediateWithSignExtend v_2896 8 8);
      v_14518 <- eval (concat (expression.bv_nat 126 0) (extract v_14516 0 2));
      v_14526 <- eval (concat (expression.bv_nat 126 0) (extract v_14516 2 4));
      v_14534 <- eval (concat (expression.bv_nat 126 0) (extract v_14516 4 6));
      v_14542 <- eval (concat (expression.bv_nat 126 0) (extract v_14516 6 8));
      setRegister (lhs.of_reg v_2895) (concat (extract (lshr v_14515 (uvalueMInt (extract (shl v_14518 5) 0 (bitwidthMInt v_14518)))) 96 128) (concat (extract (lshr v_14515 (uvalueMInt (extract (shl v_14526 5) 0 (bitwidthMInt v_14526)))) 96 128) (concat (extract (lshr v_14515 (uvalueMInt (extract (shl v_14534 5) 0 (bitwidthMInt v_14534)))) 96 128) (extract (lshr v_14515 (uvalueMInt (extract (shl v_14542 5) 0 (bitwidthMInt v_14542)))) 96 128))));
      pure ()
    pat_end
