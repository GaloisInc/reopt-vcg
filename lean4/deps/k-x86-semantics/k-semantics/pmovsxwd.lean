def pmovsxwd1 : instruction :=
  definst "pmovsxwd" $ do
    pattern fun (v_2716 : reg (bv 128)) (v_2717 : reg (bv 128)) => do
      v_5469 <- getRegister v_2716;
      setRegister (lhs.of_reg v_2717) (concat (leanSignExtend (extract v_5469 64 80) 32) (concat (leanSignExtend (extract v_5469 80 96) 32) (concat (leanSignExtend (extract v_5469 96 112) 32) (leanSignExtend (extract v_5469 112 128) 32))));
      pure ()
    pat_end;
    pattern fun (v_2712 : Mem) (v_2713 : reg (bv 128)) => do
      v_12430 <- evaluateAddress v_2712;
      v_12431 <- load v_12430 8;
      setRegister (lhs.of_reg v_2713) (concat (leanSignExtend (extract v_12431 0 16) 32) (concat (leanSignExtend (extract v_12431 16 32) 32) (concat (leanSignExtend (extract v_12431 32 48) 32) (leanSignExtend (extract v_12431 48 64) 32))));
      pure ()
    pat_end
