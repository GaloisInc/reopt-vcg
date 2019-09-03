def psrlq1 : instruction :=
  definst "psrlq" $ do
    pattern fun (v_3050 : imm int) (v_3049 : reg (bv 128)) => do
      v_8184 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3050 8 8));
      v_8186 <- getRegister v_3049;
      v_8188 <- eval (uvalueMInt v_8184);
      setRegister (lhs.of_reg v_3049) (mux (ugt v_8184 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_8186 0 64) v_8188) (lshr (extract v_8186 64 128) v_8188)));
      pure ()
    pat_end;
    pattern fun (v_3058 : reg (bv 128)) (v_3059 : reg (bv 128)) => do
      v_8199 <- getRegister v_3058;
      v_8200 <- eval (extract v_8199 64 128);
      v_8202 <- getRegister v_3059;
      v_8204 <- eval (uvalueMInt v_8200);
      setRegister (lhs.of_reg v_3059) (mux (ugt v_8200 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_8202 0 64) v_8204) (lshr (extract v_8202 64 128) v_8204)));
      pure ()
    pat_end;
    pattern fun (v_3053 : Mem) (v_3054 : reg (bv 128)) => do
      v_15153 <- evaluateAddress v_3053;
      v_15154 <- load v_15153 16;
      v_15155 <- eval (extract v_15154 64 128);
      v_15157 <- getRegister v_3054;
      v_15159 <- eval (uvalueMInt v_15155);
      setRegister (lhs.of_reg v_3054) (mux (ugt v_15155 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_15157 0 64) v_15159) (lshr (extract v_15157 64 128) v_15159)));
      pure ()
    pat_end
