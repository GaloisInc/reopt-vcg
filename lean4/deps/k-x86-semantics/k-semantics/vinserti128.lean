def vinserti1281 : instruction :=
  definst "vinserti128" $ do
    pattern fun (v_2554 : imm int) (v_2557 : reg (bv 128)) (v_2555 : reg (bv 256)) (v_2556 : reg (bv 256)) => do
      v_4293 <- getRegister v_2555;
      v_4295 <- getRegister v_2557;
      setRegister (lhs.of_reg v_2556) (mux (isBitClear (handleImmediateWithSignExtend v_2554 8 8) 7) (concat (extract v_4293 0 128) v_4295) (concat v_4295 (extract v_4293 128 256)));
      pure ()
    pat_end;
    pattern fun (v_2548 : imm int) (v_2549 : Mem) (v_2550 : reg (bv 256)) (v_2551 : reg (bv 256)) => do
      v_9735 <- getRegister v_2550;
      v_9737 <- evaluateAddress v_2549;
      v_9738 <- load v_9737 16;
      setRegister (lhs.of_reg v_2551) (mux (isBitClear (handleImmediateWithSignExtend v_2548 8 8) 7) (concat (extract v_9735 0 128) v_9738) (concat v_9738 (extract v_9735 128 256)));
      pure ()
    pat_end
