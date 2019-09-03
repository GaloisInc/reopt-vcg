def vpmovsxwq1 : instruction :=
  definst "vpmovsxwq" $ do
    pattern fun (v_2693 : reg (bv 128)) (v_2694 : reg (bv 128)) => do
      v_5647 <- getRegister v_2693;
      setRegister (lhs.of_reg v_2694) (concat (leanSignExtend (extract v_5647 96 112) 64) (leanSignExtend (extract v_5647 112 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2702 : reg (bv 128)) (v_2704 : reg (bv 256)) => do
      v_5658 <- getRegister v_2702;
      setRegister (lhs.of_reg v_2704) (concat (leanSignExtend (extract v_5658 64 80) 64) (concat (leanSignExtend (extract v_5658 80 96) 64) (concat (leanSignExtend (extract v_5658 96 112) 64) (leanSignExtend (extract v_5658 112 128) 64))));
      pure ()
    pat_end;
    pattern fun (v_2688 : Mem) (v_2689 : reg (bv 128)) => do
      v_12304 <- evaluateAddress v_2688;
      v_12305 <- load v_12304 4;
      setRegister (lhs.of_reg v_2689) (concat (leanSignExtend (extract v_12305 0 16) 64) (leanSignExtend (extract v_12305 16 32) 64));
      pure ()
    pat_end;
    pattern fun (v_2697 : Mem) (v_2699 : reg (bv 256)) => do
      v_12312 <- evaluateAddress v_2697;
      v_12313 <- load v_12312 8;
      setRegister (lhs.of_reg v_2699) (concat (leanSignExtend (extract v_12313 0 16) 64) (concat (leanSignExtend (extract v_12313 16 32) 64) (concat (leanSignExtend (extract v_12313 32 48) 64) (leanSignExtend (extract v_12313 48 64) 64))));
      pure ()
    pat_end
