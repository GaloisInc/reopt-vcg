def vpmovsxdq1 : instruction :=
  definst "vpmovsxdq" $ do
    pattern fun (v_2657 : reg (bv 128)) (v_2658 : reg (bv 128)) => do
      v_5573 <- getRegister v_2657;
      setRegister (lhs.of_reg v_2658) (concat (leanSignExtend (extract v_5573 64 96) 64) (leanSignExtend (extract v_5573 96 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2666 : reg (bv 128)) (v_2668 : reg (bv 256)) => do
      v_5584 <- getRegister v_2666;
      setRegister (lhs.of_reg v_2668) (concat (leanSignExtend (extract v_5584 0 32) 64) (concat (leanSignExtend (extract v_5584 32 64) 64) (concat (leanSignExtend (extract v_5584 64 96) 64) (leanSignExtend (extract v_5584 96 128) 64))));
      pure ()
    pat_end;
    pattern fun (v_2652 : Mem) (v_2653 : reg (bv 128)) => do
      v_12242 <- evaluateAddress v_2652;
      v_12243 <- load v_12242 8;
      setRegister (lhs.of_reg v_2653) (concat (leanSignExtend (extract v_12243 0 32) 64) (leanSignExtend (extract v_12243 32 64) 64));
      pure ()
    pat_end;
    pattern fun (v_2661 : Mem) (v_2663 : reg (bv 256)) => do
      v_12250 <- evaluateAddress v_2661;
      v_12251 <- load v_12250 16;
      setRegister (lhs.of_reg v_2663) (concat (leanSignExtend (extract v_12251 0 32) 64) (concat (leanSignExtend (extract v_12251 32 64) 64) (concat (leanSignExtend (extract v_12251 64 96) 64) (leanSignExtend (extract v_12251 96 128) 64))));
      pure ()
    pat_end
