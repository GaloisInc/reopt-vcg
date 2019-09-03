def vbroadcastsd1 : instruction :=
  definst "vbroadcastsd" $ do
    pattern fun (v_2893 : reg (bv 128)) (v_2889 : reg (bv 256)) => do
      v_5991 <- getRegister v_2893;
      v_5992 <- eval (extract v_5991 64 128);
      setRegister (lhs.of_reg v_2889) (concat (concat (concat v_5992 v_5992) v_5992) v_5992);
      pure ()
    pat_end;
    pattern fun (v_2885 : Mem) (v_2886 : reg (bv 256)) => do
      v_11430 <- evaluateAddress v_2885;
      v_11431 <- load v_11430 8;
      setRegister (lhs.of_reg v_2886) (concat (concat (concat v_11431 v_11431) v_11431) v_11431);
      pure ()
    pat_end
