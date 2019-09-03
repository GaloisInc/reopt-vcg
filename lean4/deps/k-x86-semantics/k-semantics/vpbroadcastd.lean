def vpbroadcastd1 : instruction :=
  definst "vpbroadcastd" $ do
    pattern fun (v_2705 : reg (bv 128)) (v_2706 : reg (bv 128)) => do
      v_7184 <- getRegister v_2705;
      v_7185 <- eval (extract v_7184 96 128);
      setRegister (lhs.of_reg v_2706) (concat (concat (concat v_7185 v_7185) v_7185) v_7185);
      pure ()
    pat_end;
    pattern fun (v_2714 : reg (bv 128)) (v_2715 : reg (bv 256)) => do
      v_7194 <- getRegister v_2714;
      v_7195 <- eval (extract v_7194 96 128);
      setRegister (lhs.of_reg v_2715) (concat (concat (concat (concat v_7195 v_7195) v_7195) v_7195) (concat (concat (concat v_7195 v_7195) v_7195) v_7195));
      pure ()
    pat_end;
    pattern fun (v_2700 : Mem) (v_2701 : reg (bv 128)) => do
      v_16445 <- evaluateAddress v_2700;
      v_16446 <- load v_16445 4;
      setRegister (lhs.of_reg v_2701) (concat (concat (concat v_16446 v_16446) v_16446) v_16446);
      pure ()
    pat_end;
    pattern fun (v_2709 : Mem) (v_2710 : reg (bv 256)) => do
      v_16451 <- evaluateAddress v_2709;
      v_16452 <- load v_16451 4;
      setRegister (lhs.of_reg v_2710) (concat (concat (concat (concat v_16452 v_16452) v_16452) v_16452) (concat (concat (concat v_16452 v_16452) v_16452) v_16452));
      pure ()
    pat_end
