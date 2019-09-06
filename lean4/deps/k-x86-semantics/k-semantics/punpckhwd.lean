def punpckhwd1 : instruction :=
  definst "punpckhwd" $ do
    pattern fun (v_3280 : reg (bv 128)) (v_3281 : reg (bv 128)) => do
      v_8748 <- getRegister v_3280;
      v_8750 <- getRegister v_3281;
      setRegister (lhs.of_reg v_3281) (concat (concat (extract v_8748 0 16) (extract v_8750 0 16)) (concat (concat (extract v_8748 16 32) (extract v_8750 16 32)) (concat (concat (extract v_8748 32 48) (extract v_8750 32 48)) (concat (extract v_8748 48 64) (extract v_8750 48 64)))));
      pure ()
    pat_end;
    pattern fun (v_3276 : Mem) (v_3277 : reg (bv 128)) => do
      v_15142 <- evaluateAddress v_3276;
      v_15143 <- load v_15142 16;
      v_15145 <- getRegister v_3277;
      setRegister (lhs.of_reg v_3277) (concat (concat (extract v_15143 0 16) (extract v_15145 0 16)) (concat (concat (extract v_15143 16 32) (extract v_15145 16 32)) (concat (concat (extract v_15143 32 48) (extract v_15145 32 48)) (concat (extract v_15143 48 64) (extract v_15145 48 64)))));
      pure ()
    pat_end
