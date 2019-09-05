def punpckhbw1 : instruction :=
  definst "punpckhbw" $ do
    pattern fun (v_3225 : reg (bv 128)) (v_3226 : reg (bv 128)) => do
      v_8659 <- getRegister v_3225;
      v_8661 <- getRegister v_3226;
      setRegister (lhs.of_reg v_3226) (concat (concat (extract v_8659 0 8) (extract v_8661 0 8)) (concat (concat (extract v_8659 8 16) (extract v_8661 8 16)) (concat (concat (extract v_8659 16 24) (extract v_8661 16 24)) (concat (concat (extract v_8659 24 32) (extract v_8661 24 32)) (concat (concat (extract v_8659 32 40) (extract v_8661 32 40)) (concat (concat (extract v_8659 40 48) (extract v_8661 40 48)) (concat (concat (extract v_8659 48 56) (extract v_8661 48 56)) (concat (extract v_8659 56 64) (extract v_8661 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (v_3222 : Mem) (v_3221 : reg (bv 128)) => do
      v_15113 <- evaluateAddress v_3222;
      v_15114 <- load v_15113 16;
      v_15116 <- getRegister v_3221;
      setRegister (lhs.of_reg v_3221) (concat (concat (extract v_15114 0 8) (extract v_15116 0 8)) (concat (concat (extract v_15114 8 16) (extract v_15116 8 16)) (concat (concat (extract v_15114 16 24) (extract v_15116 16 24)) (concat (concat (extract v_15114 24 32) (extract v_15116 24 32)) (concat (concat (extract v_15114 32 40) (extract v_15116 32 40)) (concat (concat (extract v_15114 40 48) (extract v_15116 40 48)) (concat (concat (extract v_15114 48 56) (extract v_15116 48 56)) (concat (extract v_15114 56 64) (extract v_15116 56 64)))))))));
      pure ()
    pat_end
