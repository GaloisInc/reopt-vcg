def movbeq1 : instruction :=
  definst "movbeq" $ do
    pattern fun (v_3227 : reg (bv 64)) (v_3226 : Mem) => do
      v_7996 <- evaluateAddress v_3226;
      v_7997 <- getRegister v_3227;
      store v_7996 (concat (concat (concat (concat (concat (concat (concat (extract v_7997 56 64) (extract v_7997 48 56)) (extract v_7997 40 48)) (extract v_7997 32 40)) (extract v_7997 24 32)) (extract v_7997 16 24)) (extract v_7997 8 16)) (extract v_7997 0 8)) 8;
      pure ()
    pat_end;
    pattern fun (v_3234 : Mem) (v_3235 : reg (bv 64)) => do
      v_9948 <- evaluateAddress v_3234;
      v_9949 <- load v_9948 8;
      setRegister (lhs.of_reg v_3235) (concat (concat (concat (concat (concat (concat (concat (extract v_9949 56 64) (extract v_9949 48 56)) (extract v_9949 40 48)) (extract v_9949 32 40)) (extract v_9949 24 32)) (extract v_9949 16 24)) (extract v_9949 8 16)) (extract v_9949 0 8));
      pure ()
    pat_end
