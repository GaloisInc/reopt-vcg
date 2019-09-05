def movbeq1 : instruction :=
  definst "movbeq" $ do
    pattern fun (v_3280 : reg (bv 64)) (v_3279 : Mem) => do
      v_7531 <- evaluateAddress v_3279;
      v_7532 <- getRegister v_3280;
      store v_7531 (concat (concat (concat (concat (concat (concat (concat (extract v_7532 56 64) (extract v_7532 48 56)) (extract v_7532 40 48)) (extract v_7532 32 40)) (extract v_7532 24 32)) (extract v_7532 16 24)) (extract v_7532 8 16)) (extract v_7532 0 8)) 8;
      pure ()
    pat_end;
    pattern fun (v_3287 : Mem) (v_3288 : reg (bv 64)) => do
      v_8998 <- evaluateAddress v_3287;
      v_8999 <- load v_8998 8;
      setRegister (lhs.of_reg v_3288) (concat (concat (concat (concat (concat (concat (concat (extract v_8999 56 64) (extract v_8999 48 56)) (extract v_8999 40 48)) (extract v_8999 32 40)) (extract v_8999 24 32)) (extract v_8999 16 24)) (extract v_8999 8 16)) (extract v_8999 0 8));
      pure ()
    pat_end
