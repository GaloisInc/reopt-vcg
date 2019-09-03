def vperm2i1281 : instruction :=
  definst "vperm2i128" $ do
    pattern fun (v_2962 : imm int) (v_2964 : reg (bv 256)) (v_2965 : reg (bv 256)) (v_2966 : reg (bv 256)) => do
      v_8170 <- eval (handleImmediateWithSignExtend v_2962 8 8);
      v_8173 <- eval (extract v_8170 2 4);
      v_8175 <- getRegister v_2965;
      v_8176 <- eval (extract v_8175 128 256);
      v_8178 <- eval (extract v_8175 0 128);
      v_8180 <- getRegister v_2964;
      v_8181 <- eval (extract v_8180 128 256);
      v_8182 <- eval (extract v_8180 0 128);
      v_8189 <- eval (extract v_8170 6 8);
      setRegister (lhs.of_reg v_2966) (concat (mux (eq (extract v_8170 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_8173 (expression.bv_nat 2 0)) v_8176 (mux (eq v_8173 (expression.bv_nat 2 1)) v_8178 (mux (eq v_8173 (expression.bv_nat 2 2)) v_8181 v_8182)))) (mux (eq (extract v_8170 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_8189 (expression.bv_nat 2 0)) v_8176 (mux (eq v_8189 (expression.bv_nat 2 1)) v_8178 (mux (eq v_8189 (expression.bv_nat 2 2)) v_8181 v_8182)))));
      pure ()
    pat_end;
    pattern fun (v_2957 : imm int) (v_2956 : Mem) (v_2958 : reg (bv 256)) (v_2959 : reg (bv 256)) => do
      v_16964 <- eval (handleImmediateWithSignExtend v_2957 8 8);
      v_16967 <- eval (extract v_16964 2 4);
      v_16969 <- getRegister v_2958;
      v_16970 <- eval (extract v_16969 128 256);
      v_16972 <- eval (extract v_16969 0 128);
      v_16974 <- evaluateAddress v_2956;
      v_16975 <- load v_16974 32;
      v_16976 <- eval (extract v_16975 128 256);
      v_16977 <- eval (extract v_16975 0 128);
      v_16984 <- eval (extract v_16964 6 8);
      setRegister (lhs.of_reg v_2959) (concat (mux (eq (extract v_16964 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_16967 (expression.bv_nat 2 0)) v_16970 (mux (eq v_16967 (expression.bv_nat 2 1)) v_16972 (mux (eq v_16967 (expression.bv_nat 2 2)) v_16976 v_16977)))) (mux (eq (extract v_16964 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_16984 (expression.bv_nat 2 0)) v_16970 (mux (eq v_16984 (expression.bv_nat 2 1)) v_16972 (mux (eq v_16984 (expression.bv_nat 2 2)) v_16976 v_16977)))));
      pure ()
    pat_end
