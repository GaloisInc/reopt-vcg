def rorx1 : instruction :=
  definst "rorx" $ do
    pattern fun (v_2861 : imm int) (v_2864 : reg (bv 32)) (v_2865 : reg (bv 32)) => do
      v_7362 <- getRegister v_2864;
      v_7365 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2861 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2865) (bv_or (lshr v_7362 v_7365) (extract (shl v_7362 (sub (expression.bv_nat 32 32) v_7365)) 0 32));
      pure ()
    pat_end;
    pattern fun (v_2884 : imm int) (v_2882 : reg (bv 64)) (v_2883 : reg (bv 64)) => do
      v_7383 <- getRegister v_2882;
      v_7386 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2884 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2883) (bv_or (lshr v_7383 v_7386) (extract (shl v_7383 (sub (expression.bv_nat 64 64) v_7386)) 0 64));
      pure ()
    pat_end;
    pattern fun (v_2851 : imm int) (v_2855 : Mem) (v_2854 : reg (bv 32)) => do
      v_11835 <- evaluateAddress v_2855;
      v_11836 <- load v_11835 4;
      v_11839 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2851 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2854) (bv_or (lshr v_11836 v_11839) (extract (shl v_11836 (sub (expression.bv_nat 32 32) v_11839)) 0 32));
      pure ()
    pat_end;
    pattern fun (v_2873 : imm int) (v_2876 : Mem) (v_2872 : reg (bv 64)) => do
      v_11846 <- evaluateAddress v_2876;
      v_11847 <- load v_11846 8;
      v_11850 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2873 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2872) (bv_or (lshr v_11847 v_11850) (extract (shl v_11847 (sub (expression.bv_nat 64 64) v_11850)) 0 64));
      pure ()
    pat_end
