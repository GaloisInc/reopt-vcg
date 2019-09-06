def movbeq1 : instruction :=
  definst "movbeq" $ do
    pattern fun (v_3307 : reg (bv 64)) (v_3306 : Mem) => do
      v_7547 <- evaluateAddress v_3306;
      v_7548 <- getRegister v_3307;
      store v_7547 (concat (concat (concat (concat (concat (concat (concat (extract v_7548 56 64) (extract v_7548 48 56)) (extract v_7548 40 48)) (extract v_7548 32 40)) (extract v_7548 24 32)) (extract v_7548 16 24)) (extract v_7548 8 16)) (extract v_7548 0 8)) 8;
      pure ()
    pat_end;
    pattern fun (v_3314 : Mem) (v_3315 : reg (bv 64)) => do
      v_9008 <- evaluateAddress v_3314;
      v_9009 <- load v_9008 8;
      setRegister (lhs.of_reg v_3315) (concat (concat (concat (concat (concat (concat (concat (extract v_9009 56 64) (extract v_9009 48 56)) (extract v_9009 40 48)) (extract v_9009 32 40)) (extract v_9009 24 32)) (extract v_9009 16 24)) (extract v_9009 8 16)) (extract v_9009 0 8));
      pure ()
    pat_end
