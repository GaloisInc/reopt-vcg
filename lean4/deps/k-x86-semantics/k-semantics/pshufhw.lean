def pshufhw1 : instruction :=
  definst "pshufhw" $ do
    pattern fun (v_2976 : imm int) (v_2974 : reg (bv 128)) (v_2975 : reg (bv 128)) => do
      v_7192 <- getRegister v_2974;
      v_7193 <- eval (handleImmediateWithSignExtend v_2976 8 8);
      setRegister (lhs.of_reg v_2975) (concat (extract (lshr v_7192 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7193 0 2)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_7192 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7193 2 4)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_7192 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7193 4 6)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_7192 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7193 6 8)) (expression.bv_nat 128 4)) 0 128)) 48 64) (extract v_7192 64 128)))));
      pure ()
    pat_end;
    pattern fun (v_2970 : imm int) (v_2971 : Mem) (v_2969 : reg (bv 128)) => do
      v_13912 <- evaluateAddress v_2971;
      v_13913 <- load v_13912 16;
      v_13914 <- eval (handleImmediateWithSignExtend v_2970 8 8);
      setRegister (lhs.of_reg v_2969) (concat (extract (lshr v_13913 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13914 0 2)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_13913 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13914 2 4)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_13913 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13914 4 6)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_13913 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13914 6 8)) (expression.bv_nat 128 4)) 0 128)) 48 64) (extract v_13913 64 128)))));
      pure ()
    pat_end
