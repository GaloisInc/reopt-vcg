def vextracti1281 : instruction :=
  definst "vextracti128" $ do
    pattern fun (v_2397 : imm int) (v_2399 : reg (bv 256)) (v_2396 : reg (bv 128)) => do
      v_4015 <- getRegister v_2399;
      setRegister (lhs.of_reg v_2396) (mux (eq (extract (handleImmediateWithSignExtend v_2397 8 8) 7 8) (expression.bv_nat 1 0)) (extract v_4015 128 256) (extract v_4015 0 128));
      pure ()
    pat_end;
    pattern fun (v_2391 : imm int) (v_2393 : reg (bv 256)) (v_2392 : Mem) => do
      v_13736 <- evaluateAddress v_2392;
      v_13740 <- getRegister v_2393;
      store v_13736 (mux (eq (extract (handleImmediateWithSignExtend v_2391 8 8) 7 8) (expression.bv_nat 1 0)) (extract v_13740 128 256) (extract v_13740 0 128)) 16;
      pure ()
    pat_end
