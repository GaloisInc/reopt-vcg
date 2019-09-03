def movddup1 : instruction :=
  definst "movddup" $ do
    pattern fun (v_2431 : reg (bv 128)) (v_2432 : reg (bv 128)) => do
      v_3859 <- getRegister v_2431;
      setRegister (lhs.of_reg v_2432) (concat (extract v_3859 64 128) (extract v_3859 64 128));
      pure ()
    pat_end;
    pattern fun (v_2427 : Mem) (v_2428 : reg (bv 128)) => do
      v_8818 <- evaluateAddress v_2427;
      v_8819 <- load v_8818 8;
      setRegister (lhs.of_reg v_2428) (concat v_8819 v_8819);
      pure ()
    pat_end
