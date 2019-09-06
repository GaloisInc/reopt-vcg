def movbel1 : instruction :=
  definst "movbel" $ do
    pattern fun (v_3291 : reg (bv 32)) (v_3290 : Mem) => do
      v_7529 <- evaluateAddress v_3290;
      v_7530 <- getRegister v_3291;
      store v_7529 (concat (concat (concat (extract v_7530 24 32) (extract v_7530 16 24)) (extract v_7530 8 16)) (extract v_7530 0 8)) 4;
      pure ()
    pat_end;
    pattern fun (v_3298 : Mem) (v_3299 : reg (bv 32)) => do
      v_8979 <- evaluateAddress v_3298;
      v_8980 <- load v_8979 4;
      setRegister (lhs.of_reg v_3299) (concat (concat (concat (extract v_8980 24 32) (extract v_8980 16 24)) (extract v_8980 8 16)) (extract v_8980 0 8));
      pure ()
    pat_end
