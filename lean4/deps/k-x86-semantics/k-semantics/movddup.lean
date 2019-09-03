def movddup1 : instruction :=
  definst "movddup" $ do
    pattern fun (v_2419 : reg (bv 128)) (v_2420 : reg (bv 128)) => do
      v_3846 <- getRegister v_2419;
      setRegister (lhs.of_reg v_2420) (concat (extract v_3846 64 128) (extract v_3846 64 128));
      pure ()
    pat_end;
    pattern fun (v_2414 : Mem) (v_2415 : reg (bv 128)) => do
      v_8839 <- evaluateAddress v_2414;
      v_8840 <- load v_8839 8;
      setRegister (lhs.of_reg v_2415) (concat v_8840 v_8840);
      pure ()
    pat_end
