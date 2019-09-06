def pshufhw1 : instruction :=
  definst "pshufhw" $ do
    pattern fun (v_3002 : imm int) (v_3003 : reg (bv 128)) (v_3004 : reg (bv 128)) => do
      v_7219 <- getRegister v_3003;
      v_7220 <- eval (handleImmediateWithSignExtend v_3002 8 8);
      setRegister (lhs.of_reg v_3004) (concat (extract (lshr v_7219 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7220 0 2)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_7219 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7220 2 4)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_7219 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7220 4 6)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_7219 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7220 6 8)) (expression.bv_nat 128 4)) 0 128)) 48 64) (extract v_7219 64 128)))));
      pure ()
    pat_end;
    pattern fun (v_2998 : imm int) (v_2997 : Mem) (v_2999 : reg (bv 128)) => do
      v_13888 <- evaluateAddress v_2997;
      v_13889 <- load v_13888 16;
      v_13890 <- eval (handleImmediateWithSignExtend v_2998 8 8);
      setRegister (lhs.of_reg v_2999) (concat (extract (lshr v_13889 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13890 0 2)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_13889 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13890 2 4)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_13889 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13890 4 6)) (expression.bv_nat 128 4)) 0 128)) 48 64) (concat (extract (lshr v_13889 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13890 6 8)) (expression.bv_nat 128 4)) 0 128)) 48 64) (extract v_13889 64 128)))));
      pure ()
    pat_end
