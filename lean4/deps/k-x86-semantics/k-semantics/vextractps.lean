def vextractps1 : instruction :=
  definst "vextractps" $ do
    pattern fun (v_2471 : imm int) (v_2474 : reg (bv 128)) (v_2472 : reg (bv 32)) => do
      v_4087 <- getRegister v_2474;
      setRegister (lhs.of_reg v_2472) (extract (lshr v_4087 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2471 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128);
      pure ()
    pat_end;
    pattern fun (v_2467 : imm int) (v_2468 : reg (bv 128)) (v_2466 : Mem) => do
      v_13837 <- evaluateAddress v_2466;
      v_13838 <- getRegister v_2468;
      store v_13837 (extract (lshr v_13838 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2467 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128) 4;
      pure ()
    pat_end
