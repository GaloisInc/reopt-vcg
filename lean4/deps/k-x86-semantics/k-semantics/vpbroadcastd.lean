def vpbroadcastd1 : instruction :=
  definst "vpbroadcastd" $ do
    pattern fun (v_2715 : reg (bv 128)) (v_2716 : reg (bv 128)) => do
      v_7047 <- getRegister v_2715;
      v_7048 <- eval (extract v_7047 96 128);
      setRegister (lhs.of_reg v_2716) (concat (concat (concat v_7048 v_7048) v_7048) v_7048);
      pure ()
    pat_end;
    pattern fun (v_2724 : reg (bv 128)) (v_2728 : reg (bv 256)) => do
      v_7057 <- getRegister v_2724;
      v_7058 <- eval (extract v_7057 96 128);
      setRegister (lhs.of_reg v_2728) (concat (concat (concat (concat v_7058 v_7058) v_7058) v_7058) (concat (concat (concat v_7058 v_7058) v_7058) v_7058));
      pure ()
    pat_end;
    pattern fun (v_2714 : Mem) (v_2711 : reg (bv 128)) => do
      v_15936 <- evaluateAddress v_2714;
      v_15937 <- load v_15936 4;
      setRegister (lhs.of_reg v_2711) (concat (concat (concat v_15937 v_15937) v_15937) v_15937);
      pure ()
    pat_end;
    pattern fun (v_2722 : Mem) (v_2723 : reg (bv 256)) => do
      v_15942 <- evaluateAddress v_2722;
      v_15943 <- load v_15942 4;
      setRegister (lhs.of_reg v_2723) (concat (concat (concat (concat v_15943 v_15943) v_15943) v_15943) (concat (concat (concat v_15943 v_15943) v_15943) v_15943));
      pure ()
    pat_end
