def movbe1 : instruction :=
  definst "movbe" $ do
    pattern fun (v_2380 : reg (bv 16)) (v_2381 : Mem) => do
      v_8822 <- evaluateAddress v_2381;
      v_8823 <- getRegister v_2380;
      store v_8822 (concat (extract v_8823 8 16) (extract v_8823 0 8)) 2;
      pure ()
    pat_end;
    pattern fun (v_2389 : Mem) (v_2388 : reg (bv 16)) => do
      v_10985 <- evaluateAddress v_2389;
      v_10986 <- load v_10985 2;
      setRegister (lhs.of_reg v_2388) (concat (extract v_10986 8 16) (extract v_10986 0 8));
      pure ()
    pat_end
