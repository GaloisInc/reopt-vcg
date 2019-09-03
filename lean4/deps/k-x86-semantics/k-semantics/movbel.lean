def movbel1 : instruction :=
  definst "movbel" $ do
    pattern fun (v_3211 : reg (bv 32)) (v_3210 : Mem) => do
      v_7978 <- evaluateAddress v_3210;
      v_7979 <- getRegister v_3211;
      store v_7978 (concat (concat (concat (extract v_7979 24 32) (extract v_7979 16 24)) (extract v_7979 8 16)) (extract v_7979 0 8)) 4;
      pure ()
    pat_end;
    pattern fun (v_3218 : Mem) (v_3219 : reg (bv 32)) => do
      v_9919 <- evaluateAddress v_3218;
      v_9920 <- load v_9919 4;
      setRegister (lhs.of_reg v_3219) (concat (concat (concat (extract v_9920 24 32) (extract v_9920 16 24)) (extract v_9920 8 16)) (extract v_9920 0 8));
      pure ()
    pat_end
