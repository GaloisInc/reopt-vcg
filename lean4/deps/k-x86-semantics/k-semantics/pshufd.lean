def pshufd1 : instruction :=
  definst "pshufd" $ do
    pattern fun (v_2965 : imm int) (v_2963 : reg (bv 128)) (v_2964 : reg (bv 128)) => do
      v_7157 <- getRegister v_2963;
      v_7158 <- eval (handleImmediateWithSignExtend v_2965 8 8);
      setRegister (lhs.of_reg v_2964) (concat (extract (lshr v_7157 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7158 0 2)) (expression.bv_nat 128 5)) 0 128)) 96 128) (concat (extract (lshr v_7157 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7158 2 4)) (expression.bv_nat 128 5)) 0 128)) 96 128) (concat (extract (lshr v_7157 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7158 4 6)) (expression.bv_nat 128 5)) 0 128)) 96 128) (extract (lshr v_7157 (extract (shl (concat (expression.bv_nat 126 0) (extract v_7158 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2959 : imm int) (v_2960 : Mem) (v_2958 : reg (bv 128)) => do
      v_13881 <- evaluateAddress v_2960;
      v_13882 <- load v_13881 16;
      v_13883 <- eval (handleImmediateWithSignExtend v_2959 8 8);
      setRegister (lhs.of_reg v_2958) (concat (extract (lshr v_13882 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13883 0 2)) (expression.bv_nat 128 5)) 0 128)) 96 128) (concat (extract (lshr v_13882 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13883 2 4)) (expression.bv_nat 128 5)) 0 128)) 96 128) (concat (extract (lshr v_13882 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13883 4 6)) (expression.bv_nat 128 5)) 0 128)) 96 128) (extract (lshr v_13882 (extract (shl (concat (expression.bv_nat 126 0) (extract v_13883 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128))));
      pure ()
    pat_end
