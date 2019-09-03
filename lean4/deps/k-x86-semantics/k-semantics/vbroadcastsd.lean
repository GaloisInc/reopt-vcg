def vbroadcastsd1 : instruction :=
  definst "vbroadcastsd" $ do
    pattern fun (v_2880 : reg (bv 128)) (v_2877 : reg (bv 256)) => do
      v_5532 <- getRegister v_2880;
      v_5533 <- eval (extract v_5532 64 128);
      setRegister (lhs.of_reg v_2877) (concat (concat (concat v_5533 v_5533) v_5533) v_5533);
      pure ()
    pat_end;
    pattern fun (v_2872 : Mem) (v_2873 : reg (bv 256)) => do
      v_9888 <- evaluateAddress v_2872;
      v_9889 <- load v_9888 8;
      setRegister (lhs.of_reg v_2873) (concat (concat (concat v_9889 v_9889) v_9889) v_9889);
      pure ()
    pat_end
