def movddup1 : instruction :=
  definst "movddup" $ do
    pattern fun (v_2507 : reg (bv 128)) (v_2508 : reg (bv 128)) => do
      v_3937 <- getRegister v_2507;
      setRegister (lhs.of_reg v_2508) (concat (extract v_3937 64 128) (extract v_3937 64 128));
      pure ()
    pat_end;
    pattern fun (v_2503 : Mem) (v_2504 : reg (bv 128)) => do
      v_8709 <- evaluateAddress v_2503;
      v_8710 <- load v_8709 8;
      setRegister (lhs.of_reg v_2504) (concat v_8710 v_8710);
      pure ()
    pat_end
