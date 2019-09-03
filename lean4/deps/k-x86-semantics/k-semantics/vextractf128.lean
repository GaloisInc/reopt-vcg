def vextractf1281 : instruction :=
  definst "vextractf128" $ do
    pattern fun (v_2399 : imm int) (v_2400 : reg (bv 256)) (v_2398 : reg (bv 128)) => do
      v_4015 <- getRegister v_2400;
      setRegister (lhs.of_reg v_2398) (mux (eq (extract (handleImmediateWithSignExtend v_2399 8 8) 7 8) (expression.bv_nat 1 0)) (extract v_4015 128 256) (extract v_4015 0 128));
      pure ()
    pat_end;
    pattern fun (v_2393 : imm int) (v_2395 : reg (bv 256)) (v_2394 : Mem) => do
      v_23603 <- evaluateAddress v_2394;
      v_23607 <- getRegister v_2395;
      store v_23603 (mux (eq (extract (handleImmediateWithSignExtend v_2393 8 8) 7 8) (expression.bv_nat 1 0)) (extract v_23607 128 256) (extract v_23607 0 128)) 16;
      pure ()
    pat_end
