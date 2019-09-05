def movbe1 : instruction :=
  definst "movbe" $ do
    pattern fun (v_2444 : reg (bv 16)) (v_2443 : Mem) => do
      v_8665 <- evaluateAddress v_2443;
      v_8666 <- getRegister v_2444;
      store v_8665 (concat (extract v_8666 8 16) (extract v_8666 0 8)) 2;
      pure ()
    pat_end;
    pattern fun (v_2451 : Mem) (v_2452 : reg (bv 16)) => do
      v_10668 <- evaluateAddress v_2451;
      v_10669 <- load v_10668 2;
      setRegister (lhs.of_reg v_2452) (concat (extract v_10669 8 16) (extract v_10669 0 8));
      pure ()
    pat_end
