def pmulld1 : instruction :=
  definst "pmulld" $ do
    pattern fun (v_2824 : reg (bv 128)) (v_2825 : reg (bv 128)) => do
      v_5813 <- getRegister v_2825;
      v_5816 <- getRegister v_2824;
      setRegister (lhs.of_reg v_2825) (concat (extract (mul (leanSignExtend (extract v_5813 0 32) 64) (leanSignExtend (extract v_5816 0 32) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_5813 32 64) 64) (leanSignExtend (extract v_5816 32 64) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_5813 64 96) 64) (leanSignExtend (extract v_5816 64 96) 64)) 32 64) (extract (mul (leanSignExtend (extract v_5813 96 128) 64) (leanSignExtend (extract v_5816 96 128) 64)) 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2820 : Mem) (v_2821 : reg (bv 128)) => do
      v_12738 <- getRegister v_2821;
      v_12741 <- evaluateAddress v_2820;
      v_12742 <- load v_12741 16;
      setRegister (lhs.of_reg v_2821) (concat (extract (mul (leanSignExtend (extract v_12738 0 32) 64) (leanSignExtend (extract v_12742 0 32) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_12738 32 64) 64) (leanSignExtend (extract v_12742 32 64) 64)) 32 64) (concat (extract (mul (leanSignExtend (extract v_12738 64 96) 64) (leanSignExtend (extract v_12742 64 96) 64)) 32 64) (extract (mul (leanSignExtend (extract v_12738 96 128) 64) (leanSignExtend (extract v_12742 96 128) 64)) 32 64))));
      pure ()
    pat_end
