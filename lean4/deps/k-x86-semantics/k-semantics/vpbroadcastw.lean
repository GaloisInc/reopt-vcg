def vpbroadcastw1 : instruction :=
  definst "vpbroadcastw" $ do
    pattern fun (v_2831 : reg (bv 128)) (v_2832 : reg (bv 128)) => do
      v_7013 <- getRegister v_2831;
      v_7014 <- eval (extract v_7013 112 128);
      setRegister (lhs.of_reg v_2832) (concat v_7014 (concat v_7014 (concat v_7014 (concat v_7014 (concat v_7014 (concat v_7014 (concat v_7014 v_7014)))))));
      pure ()
    pat_end;
    pattern fun (v_2841 : reg (bv 128)) (v_2840 : reg (bv 256)) => do
      v_7027 <- getRegister v_2841;
      v_7028 <- eval (extract v_7027 112 128);
      setRegister (lhs.of_reg v_2840) (concat v_7028 (concat v_7028 (concat v_7028 (concat v_7028 (concat v_7028 (concat v_7028 (concat v_7028 (concat v_7028 (concat v_7028 (concat v_7028 (concat v_7028 (concat v_7028 (concat v_7028 (concat v_7028 (concat v_7028 v_7028)))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2827 : Mem) (v_2828 : reg (bv 128)) => do
      v_15638 <- evaluateAddress v_2827;
      v_15639 <- load v_15638 2;
      setRegister (lhs.of_reg v_2828) (concat v_15639 (concat v_15639 (concat v_15639 (concat v_15639 (concat v_15639 (concat v_15639 (concat v_15639 v_15639)))))));
      pure ()
    pat_end;
    pattern fun (v_2836 : Mem) (v_2837 : reg (bv 256)) => do
      v_15648 <- evaluateAddress v_2836;
      v_15649 <- load v_15648 2;
      setRegister (lhs.of_reg v_2837) (concat v_15649 (concat v_15649 (concat v_15649 (concat v_15649 (concat v_15649 (concat v_15649 (concat v_15649 (concat v_15649 (concat v_15649 (concat v_15649 (concat v_15649 (concat v_15649 (concat v_15649 (concat v_15649 (concat v_15649 v_15649)))))))))))))));
      pure ()
    pat_end
