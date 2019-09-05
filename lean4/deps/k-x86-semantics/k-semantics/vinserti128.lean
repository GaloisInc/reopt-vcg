def vinserti1281 : instruction :=
  definst "vinserti128" $ do
    pattern fun (v_2529 : imm int) (v_2530 : reg (bv 128)) (v_2532 : reg (bv 256)) (v_2533 : reg (bv 256)) => do
      v_4266 <- getRegister v_2532;
      v_4268 <- getRegister v_2530;
      setRegister (lhs.of_reg v_2533) (mux (isBitClear (handleImmediateWithSignExtend v_2529 8 8) 7) (concat (extract v_4266 0 128) v_4268) (concat v_4268 (extract v_4266 128 256)));
      pure ()
    pat_end;
    pattern fun (v_2523 : imm int) (v_2524 : Mem) (v_2525 : reg (bv 256)) (v_2526 : reg (bv 256)) => do
      v_9708 <- getRegister v_2525;
      v_9710 <- evaluateAddress v_2524;
      v_9711 <- load v_9710 16;
      setRegister (lhs.of_reg v_2526) (mux (isBitClear (handleImmediateWithSignExtend v_2523 8 8) 7) (concat (extract v_9708 0 128) v_9711) (concat v_9711 (extract v_9708 128 256)));
      pure ()
    pat_end
