def vextracti1281 : instruction :=
  definst "vextracti128" $ do
    pattern fun (v_2410 : imm int) (v_2411 : reg (bv 256)) (v_2409 : reg (bv 128)) => do
      v_4028 <- getRegister v_2411;
      setRegister (lhs.of_reg v_2409) (mux (eq (extract (handleImmediateWithSignExtend v_2410 8 8) 7 8) (expression.bv_nat 1 0)) (extract v_4028 128 256) (extract v_4028 0 128));
      pure ()
    pat_end;
    pattern fun (v_2404 : imm int) (v_2406 : reg (bv 256)) (v_2405 : Mem) => do
      v_23612 <- evaluateAddress v_2405;
      v_23616 <- getRegister v_2406;
      store v_23612 (mux (eq (extract (handleImmediateWithSignExtend v_2404 8 8) 7 8) (expression.bv_nat 1 0)) (extract v_23616 128 256) (extract v_23616 0 128)) 16;
      pure ()
    pat_end
