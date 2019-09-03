def pshuflw1 : instruction :=
  definst "pshuflw" $ do
    pattern fun (v_2936 : imm int) (v_2937 : reg (bv 128)) (v_2938 : reg (bv 128)) => do
      v_7222 <- getRegister v_2937;
      v_7224 <- eval (handleImmediateWithSignExtend v_2936 8 8);
      setRegister (lhs.of_reg v_2938) (concat (extract v_7222 0 64) (concat (extract (lshr v_7222 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_7224 0 2)) 4) 0 128))) 112 128) (concat (extract (lshr v_7222 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_7224 2 4)) 4) 0 128))) 112 128) (concat (extract (lshr v_7222 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_7224 4 6)) 4) 0 128))) 112 128) (extract (lshr v_7222 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_7224 6 8)) 4) 0 128))) 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_2932 : imm int) (v_2931 : Mem) (v_2933 : reg (bv 128)) => do
      v_14111 <- evaluateAddress v_2931;
      v_14112 <- load v_14111 16;
      v_14114 <- eval (handleImmediateWithSignExtend v_2932 8 8);
      setRegister (lhs.of_reg v_2933) (concat (extract v_14112 0 64) (concat (extract (lshr v_14112 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_14114 0 2)) 4) 0 128))) 112 128) (concat (extract (lshr v_14112 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_14114 2 4)) 4) 0 128))) 112 128) (concat (extract (lshr v_14112 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_14114 4 6)) 4) 0 128))) 112 128) (extract (lshr v_14112 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_14114 6 8)) 4) 0 128))) 112 128)))));
      pure ()
    pat_end
