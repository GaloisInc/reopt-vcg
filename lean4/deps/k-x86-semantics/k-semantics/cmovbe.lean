def cmovbe1 : instruction :=
  definst "cmovbe" $ do
    pattern fun (v_2487 : Mem) (v_2490 : reg (bv 32)) => do
      v_8943 <- getRegister cf;
      v_8945 <- getRegister zf;
      v_8948 <- evaluateAddress v_2487;
      v_8949 <- load v_8948 4;
      v_8950 <- getRegister v_2490;
      setRegister (lhs.of_reg v_2490) (mux (bit_or (eq v_8943 (expression.bv_nat 1 1)) (eq v_8945 (expression.bv_nat 1 1))) v_8949 v_8950);
      pure ()
    pat_end;
    pattern fun (v_2505 : Mem) (v_2504 : reg (bv 64)) => do
      v_8953 <- getRegister cf;
      v_8955 <- getRegister zf;
      v_8958 <- evaluateAddress v_2505;
      v_8959 <- load v_8958 8;
      v_8960 <- getRegister v_2504;
      setRegister (lhs.of_reg v_2504) (mux (bit_or (eq v_8953 (expression.bv_nat 1 1)) (eq v_8955 (expression.bv_nat 1 1))) v_8959 v_8960);
      pure ()
    pat_end;
    pattern fun (v_2522 : Mem) (v_2521 : reg (bv 16)) => do
      v_8963 <- getRegister cf;
      v_8965 <- getRegister zf;
      v_8968 <- evaluateAddress v_2522;
      v_8969 <- load v_8968 2;
      v_8970 <- getRegister v_2521;
      setRegister (lhs.of_reg v_2521) (mux (bit_or (eq v_8963 (expression.bv_nat 1 1)) (eq v_8965 (expression.bv_nat 1 1))) v_8969 v_8970);
      pure ()
    pat_end
