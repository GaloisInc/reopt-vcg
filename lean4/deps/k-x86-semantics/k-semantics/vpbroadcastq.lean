def vpbroadcastq1 : instruction :=
  definst "vpbroadcastq" $ do
    pattern fun (v_2723 : reg (bv 128)) (v_2724 : reg (bv 128)) => do
      v_7205 <- getRegister v_2723;
      setRegister (lhs.of_reg v_2724) (concat (extract v_7205 64 128) (extract v_7205 64 128));
      pure ()
    pat_end;
    pattern fun (v_2732 : reg (bv 128)) (v_2733 : reg (bv 256)) => do
      v_7213 <- getRegister v_2732;
      setRegister (lhs.of_reg v_2733) (concat (concat (extract v_7213 64 128) (extract v_7213 64 128)) (concat (extract v_7213 64 128) (extract v_7213 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2718 : Mem) (v_2719 : reg (bv 128)) => do
      v_16458 <- evaluateAddress v_2718;
      v_16459 <- load v_16458 8;
      setRegister (lhs.of_reg v_2719) (concat v_16459 v_16459);
      pure ()
    pat_end;
    pattern fun (v_2727 : Mem) (v_2728 : reg (bv 256)) => do
      v_16462 <- evaluateAddress v_2727;
      v_16463 <- load v_16462 8;
      setRegister (lhs.of_reg v_2728) (concat (concat v_16463 v_16463) (concat v_16463 v_16463));
      pure ()
    pat_end
