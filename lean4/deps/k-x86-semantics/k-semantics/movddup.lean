def movddup1 : instruction :=
  definst "movddup" $ do
    pattern fun (v_2482 : reg (bv 128)) (v_2483 : reg (bv 128)) => do
      v_3910 <- getRegister v_2482;
      setRegister (lhs.of_reg v_2483) (concat (extract v_3910 64 128) (extract v_3910 64 128));
      pure ()
    pat_end;
    pattern fun (v_2477 : Mem) (v_2478 : reg (bv 128)) => do
      v_8682 <- evaluateAddress v_2477;
      v_8683 <- load v_8682 8;
      setRegister (lhs.of_reg v_2478) (concat v_8683 v_8683);
      pure ()
    pat_end
